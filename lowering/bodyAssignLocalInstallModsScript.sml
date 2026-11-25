(* Install a write inside a live local, independently of the store opcode. *)
Theory bodyAssignLocalInstallMods
Ancestors
  bodyFullPostsMods bodyFullShared bodyPtrMakeArrayCopyStateFrame
  memoryPlaceStorePost assignTuplePtrStoreWord assignTuplePtrCopyLen
  typedMemoryCopy vyperScopePreservation stateRelProj freshWrites
  vyperStorageFootprint arithmetic loweringStateRelDefs exprSimProps
  placeStore venomState bodyFullShadowBodyInv bodyPtrDefs ptrDiscipline
  loweringPosts vyperState vyperLookup compileEnv finite_map words
  placeMemoryStateRebuild robustCopyTransportPtr stmtSimDefs bodyMemoryDefs
  bodyFullHashKeccakFixed stmtSimProps bodySimFull vyperFiniteStoragePreservation

Theorem assign_local_reserved_lookup[local]:
  typed_copy_state_frame sm dest bytes s t /\ local_ptrs_reserved cenv sm ==>
  (!n p cap. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) cap) ==>
     lookup_var p t = lookup_var p s) /\
  (!p. cenv.ce_imm_alloca = SOME (Var p) ==> lookup_var p t = lookup_var p s)
Proof
  simp[typed_copy_state_frame_def, local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem assign_local_install_state[local]:
  stmt_state_rel H ctx func cenv cx ee s /\
  write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
  lookup_scopes id ee.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\ lookup_var p s = SOME w /\
  mem_path_offset entry.type path = SOME (k,ptv) /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  value_has_type ptv v /\ val_in_memory ptv v (w2n w+k) t.vs_memory /\
  typed_copy_state_frame sm (w2n w+k) bytes s t /\ bytes <= type_memory_size ptv /\
  local_ptrs_reserved cenv sm ==>
  stmt_state_rel H ctx func cenv cx ff t
Proof
  strip_tac >>
  drule_all assign_local_reserved_lookup >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory /\
   !a n. a+n <= w2n w+k \/ w2n w+k+bytes <= a ==>
     mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory` by
    (fs[typed_copy_state_frame_def, typed_copy_frame_def] >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H ctx func cenv cx ff (s with vs_memory := t.vs_memory)` by
    (irule place_store_memory_state >> conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `lookup_scopes _ _ = _`)) >>
     goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
     goal_assum (drule_at (Pat `lookup_var _ _ = SOME _`)) >> simp[] >>
     rpt strip_tac >> sym_tac >>
     qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` irule >> decide_tac) >>
  `stmt_state_rel H ctx func cenv cx ff
      (s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>)` by
    (irule (stmt_state_rel_vars_frame |> SIMP_RULE (srw_ss()) []) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ ff (s with vs_memory := _)`)) >>
     fs[lookup_var_def] >> metis_tac[]) >>
  `t = (s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) with
       <|vs_prev_bb := t.vs_prev_bb; vs_current_bb := t.vs_current_bb;
         vs_inst_idx := t.vs_inst_idx|>` by
    (qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
     simp[typed_copy_state_frame_def, venom_state_component_equality]) >>
  pop_assum SUBST1_TAC >> pure_rewrite_tac[literal_stmt_state_rel_cursor] >>
  first_assum ACCEPT_TAC
QED

Theorem assign_local_install_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\ local_ptrs_rel func cenv ee.scopes s /\
  write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
  lookup_scopes id ee.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\ lookup_var p s = SOME w /\
  mem_path_offset entry.type path = SOME (k,ptv) /\
  value_has_type entry.type entry.value /\ value_has_type ptv v /\
  (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
       val_in_memory ptv v (w2n w+k) m) /\
  typed_copy_state_frame sm (w2n w+k) bytes s t /\
  bytes <= type_memory_size ptv /\ k+bytes <= cap /\ lo <= w2n w+k /\
  local_ptrs_reserved cenv sm /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x) /\
  (!x. not_fresh_at sm x ==>
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. ~(w2n w+k <= i /\ i < w2n w+k+bytes) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) ==>
  ghost_inv_at_mods D lo d cenv cx ff Gf tf t
Proof
  strip_tac >>
  `local_region cenv ee.scopes s id (w2n w) cap` by simp[local_region_def] >>
  `!a n. a+n <= w2n w+k \/ w2n w+k+bytes <= a ==>
     mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory` by
    (fs[typed_copy_state_frame_def, typed_copy_frame_def] >> first_assum ACCEPT_TAC) >>
  `!x n. not_fresh_at sm x /\ ptr_covers G tn x s n ==> ptr_covers Gf tf x t n` by
    (rpt strip_tac >> irule ptr_covers_lookup_frame >>
     goal_assum (drule_at Any) >> fs[typed_copy_state_frame_def]) >>
  drule_all assign_local_reserved_lookup >> strip_tac >>
  qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
  simp[typed_copy_state_frame_def, venom_state_component_equality] >> strip_tac >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  rewrite_tac[ghost_inv_at_mods_def] >> conj_tac >- suspend "locals" >>
  `return_buf_ptr d cenv Gf tf t` by
    (Cases_on `d` >> gvs[return_buf_ptr_def] >> PairCases_on `x` >>
     fs[return_buf_ptr_def] >> qexistsl_tac [`x'`, `slot_size`] >> metis_tac[]) >>
  `stor_taint_ok_at D tf t` by gvs[stor_taint_ok_at_def] >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by simp[] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> `~(w2n w+k <= i /\ i < w2n w+k+bytes)` by decide_tac >> metis_tac[])
  >- metis_tac[local_ptrs_reserved_def] >>
  fs[allocas_from_def] >> metis_tac[]
QED

Resume assign_local_install_ghost[locals]:
  drule write_memory_place_entry_update >> strip_tac >> gvs[] >>
  rename1 `replace_memory_entry entry path v = INL entry'` >>
  `!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
       val_in_memory entry'.type entry'.value (w2n w) m` by
    (rpt strip_tac >> irule memory_place_replace_robust >>
     goal_assum (drule_at (Pat `replace_memory_entry _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
     qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tf.t_mem`] >>
     simp[] >> rpt conj_tac
     >- (qpat_assum `!name entry p sz. _ ==> ptr_covers _ _ _ _ _ /\ _` drule_all >> simp[])
     >- (rpt strip_tac >>
         qpat_assum `!i. _ ==> (i IN _ <=> i IN _)` (qspec_then `q` mp_tac) >>
         (impl_tac >- decide_tac) >> simp[])
     >- (rpt strip_tac >> sym_tac >>
         qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` irule >> decide_tac) >>
     first_assum ACCEPT_TAC) >>
  qx_genl_tac [`name`,`ent`,`q`,`sz`] >> strip_tac >>
  `not_fresh_at sm q` by metis_tac[local_ptrs_reserved_def] >>
  `lookup_var q t = lookup_var q s` by metis_tac[] >>
  Cases_on `name = id`
  >- (gvs[] >> metis_tac[]) >>
  `lookup_scopes name ee.scopes = SOME ent` by metis_tac[] >>
  qpat_assum `!name entry p sz. _ ==> ptr_covers _ _ _ _ _ /\ _` drule_all >>
  strip_tac >> simp[] >> rpt strip_tac >>
  `val_wf ent.type ent.value /\
   (!i. w2n w' <= i /\ i < w2n w' + val_footprint ent.type ent.value ==>
     i NOTIN {j | w2n w <= j /\ j < w2n w+cap})` by
    (irule local_region_other_footprint_ptr >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
     goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >> simp[]) >>
  irule robust_val_in_memory_exterior_frame >> simp[] >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tf.t_mem`,
    `{i | w2n w+k <= i /\ i < w2n w+k+bytes}`] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> qpat_assum `!i. _ ==> (i IN _ <=> i IN _)` (qspec_then `i` mp_tac) >> simp[])
  >- (rpt strip_tac >> qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` irule >> decide_tac) >>
  rpt strip_tac >> qpat_x_assum `!i. _ ==> i NOTIN _` (qspec_then `i` mp_tac) >>
  simp[] >> decide_tac
QED
Finalise assign_local_install_ghost

(* sm is the start of the physical write; sa is the start of the statement.
   bytes is the actual footprint (in particular it may be only a length word). *)
Theorem assign_local_install_post_mods:
  (immutable_frame_mods func cenv cx ee s /\
   local_region cenv ee.scopes s id (w2n w) cap /\
   w2n w <= w2n w+k /\ w2n w+k+bytes <= w2n w+cap /\
   typed_copy_state_frame sm (w2n w+k) bytes s t /\
   local_ptrs_reserved cenv sm /\
   ff.immutables = ee.immutables /\ MAP FDOM ff.scopes = MAP FDOM ee.scopes ==>
   immutable_frame_mods func cenv cx ff t) /\
  stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
  storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods D lo d cenv cx ee G tn s /\
  write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
  lookup_scopes id ee.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\ lookup_var p s = SOME w /\
  mem_path_offset entry.type path = SOME (k,ptv) /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  value_has_type ptv v /\
  (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory ptv v (w2n w+k) m) /\
  typed_copy_state_frame sm (w2n w+k) bytes s t /\
  bytes <= type_memory_size ptv /\ k+bytes <= cap /\ lo <= w2n w+k /\
  local_ptrs_reserved cenv sm /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x) /\
  (!x. not_fresh_at sm x ==>
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. ~(w2n w+k <= i /\ i < w2n w+k+bytes) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  sm.cs_next_var <= sb.cs_next_var /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ~block_is_terminated sb /\ ~t.vs_halted /\ alloca_history func t /\
  return_buf_frame d cenv sm s /\ return_buf_sep d cenv ee s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==> lookup_var x s = SOME u) /\
  (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP s.vs_allocas aid = SOME a) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_frame cenv es sa s0 cenv ee s ==>
  ?ce. stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\
       (~block_is_terminated sb /\ ce = cenv) /\ cenv_top_ext cenv ce ff.scopes /\
       stmt_state_rel H ctx func ce cx ff t /\ immutable_frame_mods func ce cx ff t /\
       storage_well_formed_on cx ff (FST H) /\
       return_buf_frame d ce sb t /\ alloca_history func t /\ return_buf_sep d ce ff t /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
       s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods D lo d ce cx ff Gf tf t /\
       (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==> lookup_var x t = SOME u) /\
       (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
       (!x. not_fresh_at sa x ==>
            FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame cenv es sa s0 ce ff t /\
       (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
          aid < sa.cs_next_id /\
          (!n b len. local_region cenv es.scopes s0 n b len ==>
             off+sz <= b \/ b+len <= off) /\
          off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  `MAP FDOM ff.scopes = MAP FDOM ee.scopes` by
    metis_tac[write_place_scopes_dom] >>
  `ff = ee with scopes := ff.scopes` by
    (drule write_memory_place_entry_update >> strip_tac >> first_assum ACCEPT_TAC) >>
  `ff.immutables = ee.immutables /\ storage_well_formed_on cx ff (FST H)` by
    (qpat_x_assum `ff = _` (fn th => once_rewrite_tac[th]) >>
     simp[vyperFiniteStoragePreservationTheory.storage_well_formed_on_scopes]) >>
  `local_region cenv ee.scopes s id (w2n w) cap` by simp[local_region_def] >>
  `immutable_frame_mods func cenv cx ff t` by suspend "immutable" >>
  `val_in_memory ptv v (w2n w+k) t.vs_memory` by simp[mem_agree_outside_def] >>
  `stmt_state_rel H ctx func cenv cx ff t` by suspend "state" >>
  `ghost_inv_at_mods D lo d cenv cx ff Gf tf t` by suspend "ghost" >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   !x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s` by
    (fs[typed_copy_state_frame_def, venom_state_component_equality] >>
     first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> goal_assum (drule_at Any) >> simp[]) >>
  `return_buf_sep d cenv ff t` by suspend "return_sep" >>
  `alloca_frame cenv es sa s0 cenv ff t` by suspend "allocation" >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  qexists_tac `cenv` >> simp[stmt_lands_def, cenv_top_ext_refl] >>
  conj_tac >- fs[ghost_kept_at_def] >>
  suspend "protected_taint"
QED

Resume assign_local_install_post_mods[immutable]:
  qpat_x_assum `_ ==> immutable_frame_mods func cenv cx ff t` irule >>
  simp[] >> decide_tac
QED

Resume assign_local_install_post_mods[state]:
  irule assign_local_install_state >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >> simp[]
QED

Resume assign_local_install_post_mods[ghost]:
  irule assign_local_install_ghost >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  simp[] >> metis_tac[stmt_state_rel_local_ptrs_alloca]
QED

Resume assign_local_install_post_mods[return_sep]:
  irule return_buf_sep_locals_kept >> conj_tac
  >- (rpt strip_tac >> gvs[return_buf_sep_def, allocas_from_def] >>
      first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `return_buf_sep _ _ _ _`)) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ ee s`)) >>
  qexists_tac `sm` >> simp[]
QED

Resume assign_local_install_post_mods[allocation]:
  irule alloca_frame_trans >>
  goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ ee s`)) >>
  qexists_tac `sm` >> simp[] >> irule alloca_frame_of_mem_frame >>
  simp[] >> reverse conj_tac
  >- (goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ ee s`)) >> simp[]) >>
  rpt strip_tac >>
  `off + sz <= w2n w \/ w2n w + cap <= off` by
    (first_x_assum drule >> simp[]) >>
  qpat_x_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def, typed_copy_frame_def]) >>
  qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` irule >> decide_tac
QED

Resume assign_local_install_post_mods[protected_taint]:
  rpt strip_tac >>
  `off + sz <= w2n w \/ w2n w + cap <= off` by
    (qpat_assum `alloca_frame _ _ _ _ _ ee s`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac o REWRITE_RULE [alloca_frame_def]) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     strip_tac >> first_x_assum drule >> simp[]) >>
  `i IN tn.t_mem` by
    (qpat_assum `!j. _ ==> (j IN _ <=> j IN _)` (qspec_then `i` mp_tac) >>
     (impl_tac >- decide_tac) >> simp[]) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `!a b n j. FLOOKUP _ a = SOME (b,n) /\ _ ==> j IN _` irule >>
  simp[] >> qexistsl_tac [`aid`,`off`,`sz`] >> simp[] >> first_assum ACCEPT_TAC
QED

Finalise assign_local_install_post_mods
