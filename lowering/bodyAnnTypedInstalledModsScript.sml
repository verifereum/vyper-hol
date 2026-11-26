(* Install the declaration after the destination write, using the actual
   pre-write state of the typed copy (including any source snapshot). *)
Theory bodyAnnTypedInstalledMods
Ancestors
  bodyAnnCopyInstallMods bodyLocalTypedCopyPathMods bodyMemoryDefs
  freshWrites stmtSimDeclSource stmtSimDefs typedMemoryCopy venomState vyperState

Theorem ann_copy_typed_installed_mods:
  compile_assign_value ce (Var p) LocMemory (Var xs) F loc dty sty
    (type_memory_bytes ce dty) b = ((),sf) /\
  ~(is_bytestring_type dty /\ loc <> SOME LocMemory) /\
  ~is_word_type dty /\ ~is_word_type sty /\
  fn_has_code b sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce b /\ alloca_history func s /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,len). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      len = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce sty = type_memory_size stv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_size stv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at b xs /\ not_fresh_at b p /\
  lookup_var xs s = SOME sw /\ lookup_var p s = SOME w /\
  ptr_covers G tn xs s (type_memory_size stv) /\ ptr_covers G tn p s sz /\
  type_memory_size dtv <= sz /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n w + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/ w2n w + type_memory_size dtv <= s.vs_alloca_next) /\
  (loc = SOME LocMemory ==> expr_val_at ce cx sty start b mid v (Var xs) s) /\
  (loc <> SOME LocMemory ==>
    w2n sw + type_memory_size stv <= w2n w \/
    w2n w + type_memory_size dtv <= w2n sw) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ lo <= w2n w /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!q cap. ce.ce_return_buf = SOME (PtrVar (Var q) cap) ==> not_fresh_at b q) /\
  (!q cap. ce.ce_return_pc = SOME (PtrVar (Var q) cap) ==> not_fresh_at b q) /\
  ~s.vs_halted /\ s.vs_current_bb = b.cs_current_bb /\
  s.vs_inst_idx = LENGTH b.cs_current_insts /\
  new_variable id dtv v mid = (INL (),out) /\ mid.gas_obs = [] /\
  (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
  ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
            ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
  FLOOKUP old.ce_vars id = NONE /\
  stmt_state_rel H0 ctx func old cx es s0 /\
  stmt_state_rel (J : (bool # 256 word # type_value) list # num list) ctx func ce cx mid s /\
  (!(H : (bool # 256 word # type_value) list # num list). valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid s /\ storage_well_formed_on cx mid (FST H) /\
    immutable_frame_mods func ce cx mid s /\ ghost_inv_at_mods (DF H) lo d ce cx mid G tn s) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce mid.scopes p /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  sa.cs_next_id <= inst.inst_id /\ inst.inst_id < b.cs_next_id /\
  sa.cs_next_var <= b.cs_next_var /\
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
  s0.vs_alloca_next <= s.vs_alloca_next /\ ~block_is_terminated sf /\
  return_buf_frame d ce b s /\ return_buf_sep d old es s0 /\
  local_ptrs_reserved old sa /\ MAP FDOM mid.scopes = MAP FDOM es.scopes ==>
  ?t Gf tf.
    (!tail. new_variable id dtv v (mid with gas_obs := tail) =
      (INL (),out with gas_obs := tail)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    (out with gas_obs := [] = out) /\
    (!(H : (bool # 256 word # type_value) list # num list). valid_horizon cx st0 H out.storage_trace ==>
      (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw+cap) t) ==>
      stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sf /\
      cenv_top_ext old ce out.scopes /\
      stmt_state_rel H ctx func ce cx out t /\ immutable_frame_mods func ce cx out t /\
      storage_well_formed_on cx out (FST H) /\
      return_buf_frame d ce sf t /\ alloca_history func t /\ return_buf_sep d ce out t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d ce cx out Gf tf t /\
      (!q z. not_fresh_at sa q /\ lookup_var q s0 = SOME z ==> lookup_var q t = SOME z) /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
      (!q. not_fresh_at sa q ==>
           FLOOKUP Gf q = FLOOKUP G0 q /\ op_taint tf (Var q) = op_taint tn0 (Var q)) /\
      alloca_frame old es sa s0 ce out t /\
      (!aid off len i.
        FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
        (!name a cap. local_region old es.scopes s0 name a cap ==>
                       off+len <= a \/ a+cap <= off) /\
        off <= i /\ i < off+len /\ i IN tf.t_mem ==> i IN tn0.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(loc = SOME LocMemory ==>
    expr_val_at ce cx sty start b mid v (Var xs) s /\
    ?base len. base <= w2n w /\ w2n w + type_memory_size dtv <= base + len /\
      ((?name. local_region ce mid.scopes s name base len) \/
       ?aid. aid < b.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (base,len)))` by
    (strip_tac >> conj_tac >- (first_x_assum drule >> simp[]) >>
     qexistsl_tac [`w2n w`,`sz`] >> simp[] >> disj2_tac >> qexists_tac `inst.inst_id` >> simp[]) >>
  mp_tac (Q.INST [`sa` |-> `b`, `xd` |-> `p`, `dw` |-> `w`, `cap` |-> `sz`,
                  `H0` |-> `J`] (SPEC_ALL local_typed_copy_path_mods)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`u`,`sc`,`Gu`,`tu`,`t`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac >- (drule_then ACCEPT_TAC new_variable_success_gas_obs) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `(out with gas_obs := [] = out) /\ out.storage_trace = mid.storage_trace` by
    (`stmt_res_ok lctx (FST (new_variable id dtv v mid))` by simp[stmt_res_ok_def] >>
     drule_then strip_assume_tac new_variable_admissible_success >>
     qpat_assum `new_variable _ _ _ _ = (INL (),out)` (fn th =>
       qpat_assum `new_variable _ _ _ _ = (INL (),mid with scopes := _)` mp_tac >>
       simp[NoAsms,th] >> disch_then SUBST1_TAC >>
       qpat_assum `mid.gas_obs = []` (fn g => simp[NoAsms,g,evaluation_state_component_equality]))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "transport"
QED

Resume ann_copy_typed_installed_mods[transport]:
  `sa.cs_next_id <= b.cs_next_id` by decide_tac >>
  `alloca_frame old es sa s0 ce mid u` by
    (irule alloca_frame_trans >> qexistsl_tac [`ce`,`mid`,`s`,`b`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!q. not_fresh_at sa q ==> not_fresh_at b q` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!q z. not_fresh_at sa q /\ lookup_var q s0 = SOME z ==> lookup_var q u = SOME z` by
    (rpt strip_tac >>
     qpat_assum `!q z. _ ==> lookup_var q s = SOME z` (drule_all_then assume_tac) >>
     qpat_assum `!x. not_fresh_at b x ==> _ /\ _ /\ _ /\ _`
       (qspec_then `q` mp_tac) >> simp[]) >>
  `!q. not_fresh_at sa q ==>
    FLOOKUP Gu q = FLOOKUP G0 q /\ op_taint tu (Var q) = op_taint tn0 (Var q)` by
    (rpt strip_tac >>
     qpat_assum `!q. not_fresh_at sa q ==> FLOOKUP G q = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at b x ==> _ /\ _ /\ _ /\ _`
       (qspec_then `q` mp_tac) >> simp[]) >>
  `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent` by
    (rpt strip_tac >>
     qpat_assum `!aid ent. _ ==> FLOOKUP s.vs_allocas aid = SOME ent` (drule_then assume_tac) >>
     qpat_assum `!aid ent. FLOOKUP s.vs_allocas aid = _ ==> FLOOKUP u.vs_allocas aid = _`
       (drule_then ACCEPT_TAC)) >>
  `!aid off len i.
    FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
    (!name a cap. local_region old es.scopes s0 name a cap ==>
                   off+len <= a \/ a+cap <= off) /\
    off <= i /\ i < off+len /\ i IN tu.t_mem ==> i IN tn0.t_mem` by suspend "old_taint" >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ u t` mp_tac >>
     simp[NoAsms,typed_copy_state_frame_def,venom_state_component_equality]) >>
  `return_buf_frame d ce sf t` by suspend "return_frame" >>
  suspend "install"
QED

Resume ann_copy_typed_installed_mods[old_taint]:
  rpt gen_tac >> strip_tac >>
  `!name a cap. local_region ce mid.scopes s name a cap ==>
     off+len <= a \/ a+cap <= off` by
    (qpat_assum `alloca_frame old es sa s0 ce mid s` (mp_tac o REWRITE_RULE [alloca_frame_def]) >>
     disch_then (qspecl_then [`aid`,`off`,`len`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  `FLOOKUP s.vs_allocas aid = SOME (off,len)` by
    (qpat_assum `!aid ent. _ ==> FLOOKUP s.vs_allocas aid = SOME ent` irule >> simp[]) >>
  `aid < b.cs_next_id` by decide_tac >>
  `i IN tn.t_mem` by
    (qpat_assum `!aid off len i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _`
       (qspecl_then [`aid`,`off`,`len`,`i`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!aid off len i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
    (qspecl_then [`aid`,`off`,`len`,`i`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >> first_assum ACCEPT_TAC
QED

Resume ann_copy_typed_installed_mods[return_frame]:
  irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`b`] >>
  reverse conj_tac >- (simp[] >> decide_tac) >>
  rpt strip_tac >>
  qpat_assum `!x. not_fresh_at b x ==> _ /\ _ /\ _ /\ _` (drule_then strip_assume_tac) >>
  qpat_assum `!x. not_fresh_at sc x ==> _ /\ _ /\ _` (drule_then strip_assume_tac) >> simp[]
QED

Resume ann_copy_typed_installed_mods[install]:
  qpat_assum `out.storage_trace = mid.storage_trace` (fn th => pure_once_rewrite_tac[th]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `!q. not_fresh_at b q ==> not_fresh_at sc q` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `b` >> simp[]) >>
  `!q. not_fresh_at sa q ==> not_fresh_at sc q` by
    (rpt strip_tac >> qpat_assum `!q. not_fresh_at b q ==> not_fresh_at sc q` irule >> simp[]) >>
  `!q cap. ce.ce_return_buf = SOME (PtrVar (Var q) cap) ==> not_fresh_at sc q` by
    (rpt strip_tac >> qpat_assum `!q. not_fresh_at b q ==> not_fresh_at sc q` irule >> simp[]) >>
  `!q cap. ce.ce_return_pc = SOME (PtrVar (Var q) cap) ==> not_fresh_at sc q` by
    (rpt strip_tac >> qpat_assum `!q. not_fresh_at b q ==> not_fresh_at sc q` irule >> simp[]) >>
  `!q. not_fresh_at sc q ==>
    FLOOKUP Gf q = FLOOKUP Gu q /\ op_taint tf (Var q) = op_taint tu (Var q)` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sc x ==> _ /\ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,sz)` by
    (qpat_assum `!aid ent. FLOOKUP s.vs_allocas aid = _ ==> FLOOKUP u.vs_allocas aid = _`
       (drule_then ACCEPT_TAC)) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw+cap) u` by
    (qpat_assum `t.vs_allocas = u.vs_allocas` (fn th =>
       pure_rewrite_tac[ptrDisciplineTheory.allocas_from_def,SYM th]) >>
     qpat_assum `!bw cap. _ ==> allocas_from _ t`
       (ACCEPT_TAC o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def])) >>
  `stmt_state_rel H ctx func ce cx mid u` by
    (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ s ==> _` (drule_then ACCEPT_TAC)) >>
  `immutable_frame_mods func ce cx mid u` by
    (qpat_assum `immutable_frame_mods _ _ _ _ s ==> _` irule >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at_mods (DF H) lo d ce cx mid Gu tu u` by
    (qpat_assum `!D d. ghost_inv_at_mods D _ d _ _ _ G tn s ==> _` (drule_then ACCEPT_TAC)) >>
  irule (INST_TYPE [alpha |-> ``:256``, beta |-> alpha] ann_copy_install_post_mods) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `H0` >> first_assum ACCEPT_TAC) >>
  qpat_assum `typed_copy_state_frame sc _ _ u t` (irule_at Any) >>
  qpat_assum `new_variable id dtv v mid = _` (irule_at Any) >>
  qpat_assum `ghost_inv_at_mods (DF H) lo d ce cx mid Gu tu u` (irule_at Any) >>
  qpat_assum `FLOOKUP u.vs_allocas inst.inst_id = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP ce.ce_vars id = SOME _` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[NoAsms]
QED

Finalise ann_copy_typed_installed_mods
