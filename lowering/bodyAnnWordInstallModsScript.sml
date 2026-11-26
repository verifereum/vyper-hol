(* Installing a local word after the selected linked RHS and MSTORE. *)
Theory bodyAnnWordInstallMods
Ancestors
  bodyFullAnnAssignWordPost bodyFullPostsMods bodyFullShared typedCopyOriginPtrBase
  bodyInvSplit exprLoweringProps stmtSimDefs ptrDiscipline loweringSlice
  loweringStateRelDefs bodyFullShadowBodyInv bodyPtrDefs typedMemoryCopy
  vyperState venomState finite_map words loweringPosts stmtSimDeclSource
  freshWrites exprSimOperands stateRelProj venomMemDefs vyperStatePreservation
  exprOpenPrimitives venomInst

Theorem annassign_scope_lookup[local]:
  lookup_scopes n ((sc |+ (id,decl)) :: rest) = SOME entry /\ n <> id ==>
  lookup_scopes n (sc :: rest) = SOME entry
Proof
  strip_tac >> gvs[lookup_scopes_def, FLOOKUP_UPDATE]
QED

Theorem annassign_store_local_regions[local]:
  mid.scopes = sc :: rest /\ out.scopes = (sc |+ (id,decl)) :: rest /\
  typed_copy_state_frame b (w2n w) 32 u t /\ local_ptrs_reserved ce b /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\ lookup_var p u = SOME w ==>
  !n at sz. local_region ce out.scopes t n at sz ==>
    local_region ce mid.scopes u n at sz \/ (at = w2n w /\ sz = 32)
Proof
  strip_tac >> rpt gen_tac >> simp[local_region_def] >> strip_tac >>
  rename1 `FLOOKUP ce.ce_vars n = SOME (PtrVar (Var q) sz)` >>
  rename1 `lookup_var q t = SOME z` >>
  `not_fresh_at b q` by metis_tac[local_ptrs_reserved_def] >>
  `lookup_var q u = SOME z` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
     first_x_assum (qspec_then `q` mp_tac) >> simp[]) >>
  Cases_on `n = id`
  >- gvs[] >>
  disj1_tac >> drule_all annassign_scope_lookup >> simp[] >> metis_tac[]
QED

Theorem annassign_store_immutable_frame[local]:
  immutable_frame_mods func ce cx mid u /\ out.immutables = mid.immutables /\
  typed_copy_state_frame b (w2n w) 32 u t /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,32) /\
  (!n at sz. local_region ce out.scopes t n at sz ==>
     local_region ce mid.scopes u n at sz \/ (at = w2n w /\ sz = 32)) ==>
  immutable_frame_mods func ce cx out t
Proof
  simp[immutable_frame_mods_def, immutable_alloca_sep_mods_def,
       immutables_rel_mods_def] >> strip_tac >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
   t.vs_data_section = u.vs_data_section /\
   typed_copy_frame (w2n w) 32 u.vs_memory t.vs_memory` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `!src n at sz. local_region (ce with ce_module := src) out.scopes t n at sz ==>
      local_region (ce with ce_module := src) mid.scopes u n at sz \/
      (at = w2n w /\ sz = 32)` by
    (qpat_x_assum `!n at sz. local_region ce _ _ _ _ _ ==> _` mp_tac >>
     simp[local_region_def]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `immutables_rel ce cx.txn.target src ce.ce_is_ctor out t <=>
       immutables_rel ce cx.txn.target src ce.ce_is_ctor mid t` by
        simp[immutables_rel_def] >>
      simp[] >> irule immutables_rel_mem_agree >> qexists_tac `u` >>
      fs[typed_copy_frame_def] >> rpt strip_tac >>
      `immutable_alloca_sep func (ce with ce_module := src) cx mid u` by
        (first_x_assum irule >> simp[]) >>
      `loweringStateRelDefs$regions_disjoint off (type_memory_size tv) (w2n w) 32` by
        (fs[immutable_alloca_sep_def] >> metis_tac[]) >>
      first_x_assum irule >> fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  rpt gen_tac >> strip_tac >> irule immutable_alloca_sep_frame >>
  qexistsl_tac [`u`, `mid`] >> simp[] >> metis_tac[]
QED

Theorem annassign_store_ghost_lift[local]:
  ghost_inv_at_mods D lo d ce cx mid G tn u /\
  ghost_inv_at D 0 d ce cx out Gf tnf t /\
  FLOOKUP u.vs_allocas aid = SOME (w2n w,32) /\
  typed_copy_state_frame b (w2n w) 32 u t /\
  (!i. ~(w2n w <= i /\ i < w2n w + 32) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!q. FLOOKUP Gf q = FLOOKUP G q /\ op_taint tnf (Var q) = op_taint tn (Var q)) ==>
  ghost_inv_at_mods D lo d ce cx out Gf tnf t
Proof
  strip_tac >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
   typed_copy_frame (w2n w) 32 u.vs_memory t.vs_memory` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `lo <= w2n w` by
    (fs[ghost_inv_at_mods_def, allocas_from_def] >> metis_tac[]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo u.vs_memory` by
    fs[typed_copy_frame_def] >>
  `!i. i < lo /\ i IN tnf.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `~(w2n w <= i /\ i < w2n w + 32)` by decide_tac >> metis_tac[]) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (rpt strip_tac >> metis_tac[]))
QED

Theorem annassign_ghost_zero[local]:
  ghost_inv_at_mods D lo d ce cx mid G tn u ==>
  ghost_inv_at D 0 d ce cx mid G tn u
Proof
  rw[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >> metis_tac[]
QED

Theorem annassign_store_reserved[local]:
  typed_copy_state_frame b off len u t /\ local_ptrs_reserved ce b /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p u = SOME w ==>
  lookup_var p t = SOME w /\ t.vs_allocas = u.vs_allocas
Proof
  strip_tac >>
  `not_fresh_at b p` by metis_tac[local_ptrs_reserved_def] >>
  fs[typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]
QED

Theorem annassign_store_return_sep[local]:
  return_buf_sep d old es s0 /\
  (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t) /\
  stmt_state_rel (J:(bool # 256 word # type_value) list # num list)
    ctx func old cx es s0 /\ local_ptrs_reserved old sa /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  (!n. n <> id ==> FLOOKUP ce.ce_vars n = FLOOKUP old.ce_vars n) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\ lookup_var p t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,32) /\
  MAP FDOM (sc :: rest) = MAP FDOM es.scopes /\
  out.scopes = (sc |+ (id,decl)) :: rest ==>
  return_buf_sep d ce out t
Proof
  strip_tac >> irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_allocated_local) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `FLOOKUP ce.ce_vars id = SOME _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP t.vs_allocas _ = SOME _`)) >>
  qexistsl_tac [`J`, `old`, `ctx`, `cx`, `es`, `func`, `s0`, `sa`] >> simp[] >> rpt strip_tac >>
  irule lookup_scopes_declared_other >>
  goal_assum (drule_at (Pat `lookup_scopes _ _ = SOME _`)) >> simp[]
QED

Theorem annassign_word_install_post_mods:
  gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\ is_word_type typ /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid) /\
  new_variable id tyv v mid = (INL (),out) /\
  expr_post_mods (H: (bool # 256 word # type_value) list # num list)
    ctx func ce cx e es a b entry mid v op u /\
  ghost_inv_at_mods D lo d ce cx mid G1 tn1 u /\
  fn_inst_ids_distinct func /\ FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\
  (!n. n <> id ==> FLOOKUP ce.ce_vars n = FLOOKUP old.ce_vars n) /\
  ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
            ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
  FLOOKUP old.ce_vars id = NONE /\ lookup_var p u = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,32) /\ sa.cs_next_id <= inst.inst_id /\
  ptr_covers G1 tn1 p u 32 /\ local_ptrs_reserved ce b /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  value_has_type tyv v /\ val_in_memory tyv v (w2n w) t.vs_memory /\
  typed_copy_state_frame b (w2n w) 32 u t /\
  (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==> val_in_memory tyv v (w2n w) mem) /\
  tnf.t_stor = tn1.t_stor /\ tnf.t_trans = tn1.t_trans /\ tnf.t_imm = tn1.t_imm /\
  (!i. ~(w2n w <= i /\ i < w2n w + 32) ==> (i IN tnf.t_mem <=> i IN tn1.t_mem)) /\
  (!q. FLOOKUP Gf q = FLOOKUP G1 q /\ op_taint tnf (Var q) = op_taint tn1 (Var q)) /\
  compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
  emit_void MSTORE [Var p;op] b = ((),sf) /\ fn_has_code b sf func /\
  alloca_history func u /\ u.vs_current_bb = b.cs_current_bb /\
  u.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
  t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  return_buf_frame d old sa s0 /\ ce.ce_return_buf = old.ce_return_buf /\
  cs_extends sa a /\ cs_extends a b /\ sa.cs_next_var <= a.cs_next_var /\
  a.cs_next_var <= b.cs_next_var /\ sa.cs_next_id <= a.cs_next_id /\
  s0.vs_alloca_next <= entry.vs_alloca_next /\ entry.vs_alloca_next <= u.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x entry = lookup_var x s0) /\
  (!aid z. FLOOKUP s0.vs_allocas aid = SOME z ==> FLOOKUP entry.vs_allocas aid = SOME z) /\
  ghost_kept_at lo ce es a Ga tna entry G1 tn1 /\
  alloca_frame old es sa s0 ce es entry /\ alloca_frame ce es a entry ce mid u /\
  ghost_kept_at lo old es sa G0 tn0 s0 Ga tna /\
  (!x. not_fresh_at sa x ==> FLOOKUP Ga x = FLOOKUP G0 x /\
    op_taint tna (Var x) = op_taint tn0 (Var x)) /\
  local_ptrs_reserved old sa /\
  (?J:(bool # 256 word # type_value) list # num list.
    stmt_state_rel J ctx func old cx es s0) ==>
  stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sf /\
  cenv_top_ext old ce out.scopes /\ stmt_state_rel H ctx func ce cx out t /\
  immutable_frame_mods func ce cx out t /\ storage_well_formed_on cx out (FST H) /\
  return_buf_frame d ce sf t /\ alloca_history func t /\
  (return_buf_sep d old es s0 /\ (!bw cap. d = SOME (bw,cap) ==>
    allocas_from (w2n bw + cap) t) ==> return_buf_sep d ce out t) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods D lo d ce cx out Gf tnf t /\
  (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z) /\
  (!aid z. FLOOKUP s0.vs_allocas aid = SOME z ==> FLOOKUP t.vs_allocas aid = SOME z) /\
  (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
    op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame old es sa s0 ce out t /\
  (!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n base len. local_region old es.scopes s0 n base len ==>
      off + sz <= base \/ base + len <= off) /\
    off <= i /\ i < off + sz /\ i IN tnf.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_all annassign_continuation_success >> strip_tac >>
  `out = mid with scopes :=
     (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest` by
    metis_tac[pairTheory.PAIR_EQ] >>
  `out.scopes = (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>)) :: rest /\
   out.immutables = mid.immutables` by simp[] >>
  drule annassign_ghost_zero >> strip_tac >>
  `not_local_ptr ce mid.scopes p` by metis_tac[local_ptrs_reserved_not_live] >>
  `!q. q = p \/ ~not_local_ptr ce mid.scopes q ==> not_fresh_at b q` by
    (rpt strip_tac >- metis_tac[local_ptrs_reserved_def] >>
     metis_tac[fresh_not_local_ptr]) >>
  `SND (new_variable id tyv v mid) = out` by simp[] >>
  (* Use the ordinary local frame at floor zero, then restore the linked floor. *)
  drule_all annassign_word_full_installation_post >> strip_tac >>
  qpat_assum `SND (new_variable _ _ _ _) = out` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `!n at sz. local_region ce out.scopes t n at sz ==>
      local_region ce mid.scopes u n at sz \/ (at = w2n w /\ sz = 32)` by
    (rpt strip_tac >> irule annassign_store_local_regions >>
     goal_assum (drule_at (Pat `out.scopes = _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP ce.ce_vars _ = SOME _`)) >>
     qexistsl_tac [`b`, `t`] >> simp[]) >>
  `immutable_frame_mods func ce cx out t` by
    (drule_all annassign_store_immutable_frame >> simp[]) >>
  `ghost_inv_at_mods D lo d ce cx out Gf tnf t` by
    (drule_all annassign_store_ghost_lift >> simp[]) >>
  drule_all annassign_word_full_final_frame >> strip_tac >>
  `!aid z. FLOOKUP entry.vs_allocas aid = SOME z ==> FLOOKUP u.vs_allocas aid = SOME z` by
    fs[expr_post_def] >>
  `stmt_state_rel H ctx func ce cx mid u` by fs[expr_post_def] >>
  drule_all annassign_word_full_frame_post >> strip_tac >>
  `allocas_non_overlapping u` by
    (qpat_assum `stmt_state_rel H ctx func ce cx mid u`
       (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> simp[alloca_inv_def]) >>
  drule_all annassign_store_reserved >> strip_tac >>
  `MAP FDOM (sc :: rest) = MAP FDOM es.scopes` by
    (drule eval_read_preserves_scopes_dom >> simp[]) >>
  `~block_is_terminated sf` by
    (drule emit_void_terminated >> simp[is_terminator_def]) >>
  `return_buf_sep d old es s0 /\ (!bw cap. d = SOME (bw,cap) ==>
     allocas_from (w2n bw + cap) t) ==> return_buf_sep d ce out t` by
    (strip_tac >> irule annassign_store_return_sep >>
     conj_tac >- first_assum ACCEPT_TAC >>
     goal_assum (drule_at (Pat `out.scopes = _`)) >>
     goal_assum (drule_at (Pat `return_buf_sep _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP ce.ce_vars id = SOME _`)) >>
     qexistsl_tac [`inst.inst_id`, `sa`, `w`] >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule typed_copy_state_frame_allocas_below_fmp >> simp[]) >>
  simp[stmt_lands_def] >>
  match_mp_tac (GEN_ALL (INST_TYPE [alpha |-> ``:num # num``, beta |-> ``:256``]
    annassign_word_full_taint_post)) >>
  goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
  qpat_assum `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,32)` (irule_at Any) >>
  simp[] >> qexistsl_tac [`tna`, `tn1`, `lo`, `a`, `Ga`, `G1`, `G0`] >> simp[]
QED
