(* Installation of the fresh local at the endpoint of the physical copy. *)
Theory bodyAnnCopyInstallMods
Ancestors
  bodyFullPostsMods bodyFullShared stmtSimDeclCopyFrame stmtSimDeclSource
  typedMemoryCopy venomState venomMemDefs exprSimStorageCopy stateRelProj
  localPtrsProps assignTuplePtrCopyLen robustCopyTransportPtr exprSimProps
  exprLoweringProps loweringSlice vyperStorageFootprint bodyInvSplit
  loweringStateRelDefs bodyFullShadowBodyInv ptrDiscipline bodyPtrDefs
  vyperState finite_map loweringPosts stmtSimDefs

(* An allocated but not-yet-live local is already covered by every module's
   ALLOCA separation.  This protects the copy as well as the new live range. *)
Triviality ann_copy_install_immutables:
  immutable_frame_mods func ce cx mid s /\ out.immutables = mid.immutables /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (dest,sz) /\ n <= sz /\
  typed_copy_state_frame b dest n s t /\
  (!name a cap. local_region ce out.scopes t name a cap ==>
      local_region ce mid.scopes s name a cap \/ (a = dest /\ cap = sz)) ==>
  immutable_frame_mods func ce cx out t
Proof
  strip_tac >>
  `t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_alloca_sep_mods_def] >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `immutables_rel ce cx.txn.target src ce.ce_is_ctor mid t` suffices_by
        simp[immutables_rel_def] >>
      irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
      conj_tac >- fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
      rpt strip_tac >>
      `immutable_alloca_sep func (ce with ce_module := src) cx mid s` by metis_tac[] >>
      `regions_disjoint off (type_memory_size tv) dest sz` by
        (pop_assum (mp_tac o REWRITE_RULE [immutable_alloca_sep_def]) >>
         simp[] >> strip_tac >>
         first_x_assum (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >>
         simp[] >> disch_then strip_assume_tac >> first_x_assum drule_all >> simp[]) >>
      fs[regions_disjoint_def, typed_copy_state_frame_def, typed_copy_frame_def] >>
      first_x_assum irule >> decide_tac) >>
  rpt gen_tac >> disch_tac >> irule immutable_alloca_sep_frame >>
  qexistsl_tac [`s`,`mid`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `local_region ce out.scopes t id b' sz'` by fs[local_region_def] >>
  qpat_assum `!name a cap. local_region ce out.scopes t name a cap ==> _`
    (drule_then strip_assume_tac)
  >- (disj1_tac >> qexists_tac `id` >> fs[local_region_def]) >>
  disj2_tac >> disj1_tac >> qexists_tac `inst` >> simp[]
QED

(* Transfer the robust memory fact for an old binding, using its own
   footprint instead of requiring the entire memory to be unchanged. *)
Triviality ann_copy_old_value:
  val_wf tv v /\ regions_disjoint dest cap a room /\
  val_footprint tv v <= room /\ n <= cap /\
  typed_copy_frame dest n mem mem' /\
  (!i. ~(dest <= i /\ i < dest+n) ==> (i IN tt <=> i IN tn)) /\
  (!m. mem_agree_outside tn mem m ==> val_in_memory tv v a m) /\
  mem_agree_outside tt mem' m ==>
  val_in_memory tv v a m
Proof
  strip_tac >> irule robust_val_in_memory_exterior_frame >> simp[] >>
  qexistsl_tac [`mem`,`mem'`,`tn`,`tt`,`{i | dest <= i /\ i < dest+n}`] >>
  simp[] >> conj_tac
  >- (fs[typed_copy_frame_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qpat_x_assum `regions_disjoint _ _ _ _` mp_tac >>
  simp[regions_disjoint_def] >> decide_tac
QED

Triviality ann_copy_scope_lookup:
  lookup_scopes name ((sc |+ (id,entry))::rest) =
  if name = id then SOME entry else lookup_scopes name (sc::rest)
Proof
  Cases_on `name = id` >> simp[lookup_scopes_def,FLOOKUP_UPDATE]
QED

Triviality ann_copy_install_ghost:
  ghost_inv_at_mods D lo d ce cx mid G tn s /\
  mid.scopes = sc::rest /\ out.scopes = (sc |+ (id,entry))::rest /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p t = SOME w /\ ptr_covers Gf tf p t sz /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem) /\
  (!q k. ce.ce_return_buf = SOME (PtrVar (Var q) k) ==> not_fresh_at b q) /\
  (!q k. ce.ce_return_pc = SOME (PtrVar (Var q) k) ==> not_fresh_at b q) /\
  local_ptrs_reserved ce b /\
  (!q. not_fresh_at b q ==>
       FLOOKUP Gf q = FLOOKUP G q /\ op_taint tf (Var q) = op_taint tn (Var q)) /\
  typed_copy_state_frame b (w2n w) n s t /\ n <= sz /\ lo <= w2n w /\
  (!i. ~(w2n w <= i /\ i < w2n w+n) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!name e q cap a. lookup_scopes name mid.scopes = SOME e /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var q) cap) /\ lookup_var q s = SOME a ==>
     val_wf e.type e.value /\ val_footprint e.type e.value <= cap /\
     regions_disjoint (w2n w) sz (w2n a) cap) ==>
  ghost_inv_at_mods D lo d ce cx out Gf tf t
Proof
  strip_tac >>
  `!q k. not_fresh_at b q /\ ptr_covers G tn q s k ==> ptr_covers Gf tf q t k` by
    (rpt strip_tac >> irule ptr_covers_lookup_frame >>
     fs[typed_copy_state_frame_def] >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (fs[typed_copy_state_frame_def,typed_copy_frame_def] >> first_x_assum irule >> simp[]) >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o SRULE [typed_copy_state_frame_def,venom_state_component_equality]) >>
  rewrite_tac[ghost_inv_at_mods_def] >> conj_tac >- suspend "locals" >>
  fs[ghost_inv_at_mods_def,stor_taint_ok_at_def,allocas_from_def] >>
  rpt conj_tac
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[])
  >- (rpt strip_tac >>
      qpat_assum `!i. i < lo /\ i IN tn.t_mem ==> _` irule >>
      simp[] >> qpat_assum `!i. _ ==> (i IN tf.t_mem <=> _)`
        (qspec_then `i` mp_tac) >> simp[] >> decide_tac)
  >- (rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  first_assum ACCEPT_TAC
QED

Resume ann_copy_install_ghost[locals]:
  rpt gen_tac >> simp[ann_copy_scope_lookup] >> Cases_on `name = id`
  >- (strip_tac >> gvs[]) >>
  simp[] >> strip_tac >>
  rename1 `FLOOKUP ce.ce_vars name = SOME (PtrVar (Var q) cap)` >>
  `lookup_scopes name mid.scopes = SOME entry'` by simp[] >>
  `not_fresh_at b q` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  qpat_x_assum `!name e q cap. _ ==> ptr_covers _ _ _ _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `lookup_var q t = SOME a` >>
  `lookup_var q s = SOME a` by metis_tac[] >>
  qpat_x_assum `!name e q cap a. _ ==> _` (drule_all_then strip_assume_tac) >>
  irule ann_copy_old_value >>
  qpat_assum `regions_disjoint _ _ _ _` (irule_at Any) >>
  qpat_assum `typed_copy_frame _ _ _ _` (irule_at Any) >>
  qpat_assum `mem_agree_outside _ _ _` (irule_at Any) >>
  qexists_tac `tn.t_mem` >> simp[]
QED

Finalise ann_copy_install_ghost

Triviality ann_copy_old_alloca_frame:
  alloca_frame old es sa s0 ce mid s /\
  (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id ==>
     off+len <= dest \/ dest+sz <= off) /\
  typed_copy_frame dest n s.vs_memory t.vs_memory /\ n <= sz /\
  (!id a cap. local_region ce out.scopes t id a cap ==>
      local_region ce mid.scopes s id a cap \/ (a = dest /\ cap = sz)) ==>
  alloca_frame old es sa s0 ce out t
Proof
  simp[alloca_frame_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `!aid off len. _ ==> _ \/ _` (drule_all_then assume_tac) >>
  qpat_x_assum `!aid off sz. _ ==> _ /\ _` (drule_all_then strip_assume_tac) >>
  conj_tac
  >- (`mem_bytes_at off sz' t.vs_memory = mem_bytes_at off sz' s.vs_memory` suffices_by simp[] >>
      fs[typed_copy_frame_def] >> first_x_assum irule >> decide_tac) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!id a cap. local_region ce out.scopes t id a cap ==> _`
    (drule_then strip_assume_tac)
  >- (qpat_assum `!name a cap. local_region ce mid.scopes s name a cap ==> _`
        (drule_then ACCEPT_TAC)) >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem ann_copy_install_post_mods:
  new_variable id tyv v mid = (INL (),out) /\
  (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
  ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
            ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
  FLOOKUP old.ce_vars id = NONE /\
  stmt_state_rel H ctx func ce cx mid s /\
  storage_well_formed_on cx mid (FST H) /\
  immutable_frame_mods func ce cx mid s /\
  ghost_inv_at_mods D lo d ce cx mid G tn s /\ fn_inst_ids_distinct func /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce mid.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  sa.cs_next_id <= inst.inst_id /\ ptr_covers G tn p s sz /\
  local_ptrs_reserved ce b /\
  (!q cap. ce.ce_return_buf = SOME (PtrVar (Var q) cap) ==> not_fresh_at b q) /\
  (!q cap. ce.ce_return_pc = SOME (PtrVar (Var q) cap) ==> not_fresh_at b q) /\
  (!q. not_fresh_at sa q ==> not_fresh_at b q) /\
  n <= type_memory_size tyv /\ type_memory_size tyv <= sz /\
  val_wf tyv v /\ value_has_type tyv v /\
  typed_copy_state_frame b (w2n w) n s t /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
         val_in_memory tyv v (w2n w) mem) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. ~(w2n w <= i /\ i < w2n w+n) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  (!q. not_fresh_at b q ==>
       FLOOKUP Gf q = FLOOKUP G q /\ op_taint tf (Var q) = op_taint tn (Var q)) /\
  alloca_frame old es sa s0 ce mid s /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP s.vs_allocas aid = SOME ent) /\
  (!aid off len i.
     FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
     (!name a cap. local_region old es.scopes s0 name a cap ==>
                    off+len <= a \/ a+cap <= off) /\
     off <= i /\ i < off+len /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
  (!q z. not_fresh_at sa q /\ lookup_var q s0 = SOME z ==> lookup_var q s = SOME z) /\
  (!q. not_fresh_at sa q ==>
       FLOOKUP G q = FLOOKUP G0 q /\ op_taint tn (Var q) = op_taint tn0 (Var q)) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
  t.vs_inst_idx = LENGTH sf.cs_current_insts /\ ~block_is_terminated sf /\
  return_buf_frame d ce sf t /\ alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  return_buf_sep d old es s0 /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw+capacity) s) /\
  stmt_state_rel H0 ctx func old cx es s0 /\ local_ptrs_reserved old sa /\
  MAP FDOM mid.scopes = MAP FDOM es.scopes ==>
  stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sf /\
  cenv_top_ext old ce out.scopes /\
  stmt_state_rel H ctx func ce cx out t /\ immutable_frame_mods func ce cx out t /\
  storage_well_formed_on cx out (FST H) /\
  return_buf_frame d ce sf t /\ alloca_history func t /\ return_buf_sep d ce out t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods D lo d ce cx out Gf tf t /\
  (!q z. not_fresh_at sa q /\ lookup_var q s0 = SOME z ==> lookup_var q t = SOME z) /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
  (!q. not_fresh_at sa q ==>
       FLOOKUP Gf q = FLOOKUP G0 q /\ op_taint tf (Var q) = op_taint tn0 (Var q)) /\
  alloca_frame old es sa s0 ce out t /\
  (!aid off len i.
     FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
     (!name a cap. local_region old es.scopes s0 name a cap ==>
                    off+len <= a \/ a+cap <= off) /\
     off <= i /\ i < off+len /\ i IN tf.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  `?sc rest. mid.scopes = sc::rest /\ lookup_scopes id mid.scopes = NONE /\
      out = mid with scopes :=
          (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>))::rest`
    by suspend "scope" >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   copy_static t = copy_static s /\ typed_copy_frame (w2n w) n s.vs_memory t.vs_memory /\
   (!q. not_fresh_at b q ==> lookup_var q t = lookup_var q s)` by
    fs[typed_copy_state_frame_def,copy_static_def,venom_state_component_equality] >>
  `FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,sz)` by simp[] >>
  `!name q cap. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var q) cap) ==>
                 not_fresh_at b q` by metis_tac[local_ptrs_reserved_def] >>
  `lookup_var p t = SOME w` by metis_tac[] >>
  `n <= sz` by decide_tac >>
  `!name a cap. local_region ce out.scopes t name a cap ==>
           local_region ce mid.scopes s name a cap \/ (a = w2n w /\ cap = sz)`
    by suspend "local_regions" >>
  `cenv_top_ext old ce out.scopes` by suspend "cenv" >>
  `stmt_state_rel H ctx func ce cx out t` by suspend "state" >>
  `immutable_frame_mods func ce cx out t` by suspend "immutables" >>
  `storage_well_formed_on cx out (FST H)` by suspend "storage" >>
  `ghost_inv_at_mods D lo d ce cx out Gf tf t` by suspend "ghost" >>
  `return_buf_sep d ce out t` by suspend "return_sep" >>
  `!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id ==>
      off+len <= w2n w \/ w2n w+sz <= off` by suspend "old_separation" >>
  `alloca_frame old es sa s0 ce out t` by suspend "old_frame" >>
  simp[stmt_lands_def, GSYM arithmeticTheory.ADD_ASSOC] >> suspend "old_taint"
QED

Resume ann_copy_install_post_mods[scope]:
  `stmt_res_ok lctx (FST (new_variable id tyv v mid))` by simp[stmt_res_ok_def] >>
  drule_then strip_assume_tac new_variable_admissible_success >>
  qexistsl_tac [`sc`,`rest`] >> gvs[]
QED

Resume ann_copy_install_post_mods[local_regions]:
  rw[local_region_def] >>
  Cases_on `name = id` >> gvs[ann_copy_scope_lookup] >>
  metis_tac[]
QED

Resume ann_copy_install_post_mods[cenv]:
  simp[cenv_top_ext_def] >> rpt strip_tac >>
  `n' = id` by metis_tac[] >> gvs[] >>
  qpat_x_assum `lookup_scopes id _ = NONE` mp_tac >> simp[lookup_scopes_def,CaseEq "option"]
QED

Resume ann_copy_install_post_mods[state]:
  simp[] >> irule stmt_state_rel_declare_copy_frame >> simp[] >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  qpat_assum `typed_copy_frame _ _ _ _` (strip_assume_tac o REWRITE_RULE [typed_copy_frame_def]) >>
  qexistsl_tac [`inst`,`b`,`w`] >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac >- (qpat_assum `!name q cap. FLOOKUP ce.ce_vars name = SOME _ ==> _`
                (drule_then ACCEPT_TAC)) >>
  conj_tac >- fs[] >>
  qpat_assum `!mem. mem_agree_outside _ _ mem ==> _` irule >>
  simp[bodyPtrDefsTheory.mem_agree_outside_def]
QED

Resume ann_copy_install_post_mods[immutables]:
  irule ann_copy_install_immutables >>
  qpat_assum `immutable_frame_mods _ _ _ _ _` (irule_at Any) >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _` (irule_at Any) >>
  qpat_assum `FLOOKUP s.vs_allocas inst.inst_id = SOME _` (irule_at Any) >> simp[]
QED

Resume ann_copy_install_post_mods[storage]:
  irule (iffRL storage_well_formed_on_backends) >> qexists_tac `mid` >> simp[]
QED

Resume ann_copy_install_post_mods[ghost]:
  `ptr_covers Gf tf p t sz` by
    (irule ptr_covers_lookup_frame >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `lo <= w2n w` by
    (fs[ghost_inv_at_mods_def,allocas_from_def] >> metis_tac[]) >>
  irule ann_copy_install_ghost >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `FLOOKUP ce.ce_vars id = SOME _` (irule_at Any) >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _` (irule_at Any) >>
  qpat_assum `mid.scopes = sc::rest` (irule_at Any) >>
  qexists_tac `<|assignable := T; type := tyv; value := v; popped := []|>` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func ce mid.scopes s /\ alloca_inv s` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `local_region ce mid.scopes s name (w2n a) cap` by
    (simp[local_region_def] >> metis_tac[]) >>
  `regions_disjoint (w2n w) sz (w2n a) cap` by
    (irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >> metis_tac[]) >>
  `lookup_scopes name mid.scopes = SOME e` by simp[] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
  qpat_assum `!name entry p sz. _ ==> ?w. _` (drule_all_then strip_assume_tac) >>
  gvs[] >> drule val_footprint_le >> decide_tac
QED

Resume ann_copy_install_post_mods[return_sep]:
  irule (INST_TYPE [alpha |-> beta] return_buf_sep_allocated_local) >>
  qpat_assum `return_buf_sep d old es s0` (irule_at Any) >>
  qpat_assum `FLOOKUP ce.ce_vars id = SOME _` (irule_at Any) >>
  qpat_assum `lookup_var p t = SOME w` (irule_at Any) >>
  qexistsl_tac [`sa`,`func`,`cx`,`ctx`,`inst.inst_id`,`H0`] >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!bw capacity. _ ==> allocas_from _ s`
        (drule_then (assume_tac o REWRITE_RULE [allocas_from_def])) >>
      simp[allocas_from_def] >> rpt gen_tac >> disch_tac >>
      qpat_assum `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> _`
        (drule_then mp_tac) >> decide_tac) >>
  rpt strip_tac >> irule lookup_scopes_declared_other >>
  goal_assum (drule_at (Pat `lookup_scopes _ ((_ |+ _) :: _) = SOME _`)) >> fs[]
QED

Resume ann_copy_install_post_mods[old_separation]:
  rpt strip_tac >>
  `allocas_non_overlapping s` by
     metis_tac[stmt_state_rel_local_ptrs_alloca,alloca_inv_def] >>
  `FLOOKUP s.vs_allocas aid = SOME (off,len)` by metis_tac[] >>
  `aid <> inst.inst_id` by decide_tac >>
  fs[allocas_non_overlapping_def] >>
  qpat_assum `!a1 a2 b1 sz1 b2 sz2. _` (drule_all_then mp_tac) >> decide_tac
QED

Resume ann_copy_install_post_mods[old_frame]:
  irule ann_copy_old_alloca_frame >>
  qpat_assum `alloca_frame _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `typed_copy_frame _ _ _ _` (irule_at Any) >>
  qexists_tac `sz` >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!aid off len. _ ==> _ \/ _` (drule_all_then mp_tac) >> decide_tac
QED

Resume ann_copy_install_post_mods[old_taint]:
  rpt gen_tac >> strip_tac >>
  `off+len <= w2n w \/ w2n w+sz <= off` by
    (qpat_assum `!aid off len. _ ==> _ \/ _` (drule_all_then ACCEPT_TAC)) >>
  `i IN tn.t_mem` by
    (qpat_assum `!i. _ ==> (i IN tf.t_mem <=> _)` (qspec_then `i` mp_tac) >>
     simp[] >> decide_tac) >>
  qpat_assum `!aid off len i. _ ==> i IN tn0.t_mem`
    (qspecl_then [`aid`,`off`,`len`,`i`] mp_tac) >>
  fs[arithmeticTheory.ADD_COMM] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Finalise ann_copy_install_post_mods
