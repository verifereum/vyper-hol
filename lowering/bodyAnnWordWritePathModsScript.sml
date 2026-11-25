(* The word store at the selected successful linked RHS endpoint. *)
Theory bodyAnnWordWritePathMods
Ancestors
  bodyFullPostsMods bodySimStmtFacts exprBodyPreProps stmtSimDeclSource
  bodyFullHashKeccakFixed logStoreDataOriginPtr exprSimOperands
  exprLoweringProps vyperTypeExprSoundness exprSimHypsDefs vyperTypeInvariants
  bodyFullShadowBodyInv bodyPtrDefs loweringStateRelDefs loweringPosts
  ptrDiscipline vyperStorageFootprint

Theorem annassign_read_has_type_mods[local]:
  expr_body_pre_mods mods ce cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid) ==>
  value_has_type tyv v
Proof
  strip_tac >>
  `(expr_body_pre_mods mods ce cx env e (es with gas_obs := gs) <=>
    expr_body_pre_mods mods ce cx env e es)` by
    simp_tac (srw_ss()) [expr_body_pre_mods_def, expr_sim_inv_mods_def] >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`)
    (SIMP_RULE (srw_ss() ++ ETA_ss) [] expr_body_pre_eval_mods) >>
  disch_then (drule_then strip_assume_tac) >>
  drule expr_sim_inv_mods_env >>
  simp[env_consistent_def, env_context_consistent_def] >>
  strip_tac >> fs[value_runtime_typed_def] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem annassign_word_rhs_address[local]:
  expr_post_mods H ctx func ce cx e es a b entry mid v op u /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  ghost_kept_at lo ce es a Ga tna entry G1 tn1 /\
  ptr_covers Ga tna p entry 32 /\ not_fresh_at a p /\
  lookup_var p entry = SOME w /\ FLOOKUP entry.vs_allocas aid = SOME (w2n w,32) ==>
  lookup_var p u = SOME w /\ FLOOKUP u.vs_allocas aid = SOME (w2n w,32) /\
  ptr_covers G1 tn1 p u 32 /\ eval_operand op u = SOME (typed_val_to_w256 tyv v) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u)
Proof
  simp[expr_post_mods_def, expr_post_def] >> strip_tac >>
  `lookup_var p u = SOME w` by metis_tac[] >>
  `FLOOKUP u.vs_allocas aid = SOME (w2n w,32)` by metis_tac[] >>
  `ptr_covers G1 tn1 p u 32` by
    (qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `ptr_covers Ga tna p entry 32` mp_tac >>
     simp[ptr_covers_def, ghost_kept_at_def] >> metis_tac[]) >>
  `eval_operand op u = SOME (typed_val_to_w256 tyv v)` by
    fs[expr_val_rel_def, post_value_type_word] >>
  simp[] >> drule stmt_state_rel_allocas_below_fmp >> simp[]
QED

Theorem annassign_word_store_fresh[local]:
  local_ptrs_reserved ce a /\ a.cs_next_var <= b.cs_next_var /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\
  lookup_scopes id scopes = NONE ==>
  not_local_ptr ce scopes p /\ local_ptrs_reserved ce b /\
  (!q. q = p \/ ~not_local_ptr ce scopes q ==> not_fresh_at b q)
Proof
  strip_tac >>
  `local_ptrs_reserved ce b` by metis_tac[local_ptrs_reserved_next_var] >>
  conj_tac >- metis_tac[local_ptrs_reserved_not_live] >>
  simp[] >> rpt strip_tac
  >- metis_tac[local_ptrs_reserved_def] >>
  CCONTR_TAC >> metis_tac[fresh_not_local_ptr]
QED

Theorem annassign_word_write_path_mods:
  gas_admissible (eval_stmt cx (AnnAssign id (expr_type e) e)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
    (res,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    (?v. res = INL v /\ expr_post_mods H ctx func ce cx e es a b entry mid v op u /\
      u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func u /\ entry.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx mid G1 tn1 u /\
      ptr_val_ok cx (post_value_type ce e) v op G1 tn1 u /\
      ghost_kept_at lo ce es a Ga tna entry G1 tn1) /\ ~u.vs_halted /\ mid.gas_obs = []) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  is_word_type (expr_type e) /\ expr_body_pre_mods mods ce cx env e es /\
  local_ptrs_reserved ce a /\ a.cs_next_var <= b.cs_next_var /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) 32) /\
  ptr_covers Ga tna p entry 32 /\ not_fresh_at a p /\
  lookup_var p entry = SOME w /\ FLOOKUP entry.vs_allocas aid = SOME (w2n w,32) /\
  w2n w + 32 < dimword (:256) /\ w2n w + 32 <= entry.vs_alloca_next /\
  emit_void MSTORE [Var p;op] b = ((),sf) /\ fn_has_code b sf func ==>
  ?v sc rest out t Gf tnf.
    res = INL v /\ value_has_type tyv v /\
    mid.scopes = sc::rest /\ lookup_scopes id mid.scopes = NONE /\
    out = mid with scopes :=
      (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>))::rest /\
    (!tail. new_variable id tyv v (mid with gas_obs := tail) =
      (INL (),out with gas_obs := tail)) /\
    not_local_ptr ce mid.scopes p /\ local_ptrs_reserved ce b /\
    (!q. q = p \/ ~not_local_ptr ce mid.scopes q ==> not_fresh_at b q) /\
    lookup_var p u = SOME w /\ FLOOKUP u.vs_allocas aid = SOME (w2n w,32) /\
    ptr_covers G1 tn1 p u 32 /\ lo <= w2n w /\
    alloca_history func u /\ entry.vs_alloca_next <= u.vs_alloca_next /\
    u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
    ghost_kept_at lo ce es a Ga tna entry G1 tn1 /\ mid.gas_obs = [] /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G1,tn1) [] (OK t,Gf,tnf)) /\
    val_in_memory tyv v (w2n w) t.vs_memory /\
    typed_copy_state_frame b (w2n w) 32 u t /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    tnf.t_imm = tn1.t_imm /\ tnf.t_stor = tn1.t_stor /\ tnf.t_trans = tn1.t_trans /\
    (!i. ~(w2n w <= i /\ i < w2n w + 32) ==> (i IN tnf.t_mem <=> i IN tn1.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory tyv v (w2n w) mem) /\
    (!q. FLOOKUP Gf q = FLOOKUP G1 q /\ op_taint tnf (Var q) = op_taint tn1 (Var q))
Proof
  strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- fs[storage_trace_domain_def] >> strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac annassign_word_rhs_address >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  fs[vyperStateTheory.evaluation_state_component_equality] >>
  drule_all_then assume_tac annassign_read_has_type_mods >>
  drule_all_then strip_assume_tac annassign_continuation_all_tails >>
  drule_all_then strip_assume_tac annassign_word_store_fresh >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `lo <= w2n w` by (fs[allocas_from_def] >> metis_tac[]) >>
  `w2n w + 32 <= u.vs_alloca_next` by decide_tac >>
  `op_taint tn1 op = {}` by fs[ptr_val_ok_def] >>
  `compile_store_memory ce op (Var p) (expr_type e) (expr_type e) b = ((),sf)` by
    simp[contextTheory.compile_store_memory_def] >>
  drule_all compile_store_memory_word_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`sc`,`rest`,`t`,`Gf`,`tnf`] >> simp[] >> metis_tac[]
QED
