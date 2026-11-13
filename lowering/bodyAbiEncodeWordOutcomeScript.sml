(* Refine the recursive word argument outcome without changing exceptional exits. *)
Theory bodyAbiEncodeWordOutcome
Ancestors
  bodyAbiEncodeWordSource exprSimMemDefs loweringPosts

Theorem abi_encode_word_source_outcome:
  expr_sim_mem ctx func ce cx (expr_type e) e es /\
  is_word_type (expr_type e) /\
  lower_value compile_expr ce (expr_type e) e sa = (src,ready) /\
  fn_has_code sa ready func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!v ee s. expr_post ctx func ce cx e es sa ready s0 ee v src s ==>
     value_has_type tv v /\ ?av. vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee s. ?v at rv w av. res = INL v /\
      expr_post ctx func ce cx e es sa ready s0 ee v src s /\
      expr_store_bound cx (expr_type e) v src s /\
      s.vs_current_bb = ready.cs_current_bb /\
      s.vs_inst_idx = LENGTH ready.cs_current_insts /\
      alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
      value_has_type tv v /\
      vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
      eval_operand src s = SOME w /\ has_type at rv /\
      ~is_dynamic at /\ static_length at = 32 /\
      word_to_bytes w T = enc at rv /\
      enc at rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE[expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `ready`, `src`, `s0`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >> irule gas_outcome_post_mono >>
  qpat_assum `gas_outcome _ _ _ _ _ _ _` (irule_at Any) >>
  simp_tac bool_ss [] >> rpt strip_tac >>
  rename1 `expr_post ctx func ce cx e es sa ready s0 ee v src s` >>
  `value_has_type tv v /\ ?av. vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av` by
    metis_tac[] >>
  `expr_val_rel cx (expr_type e) v src s` by fs[expr_post_def] >>
  drule_all abi_encode_word_source_rep >> strip_tac >>
  qexistsl_tac [`v`, `at`, `rv`, `w`, `av`] >> asm_rewrite_tac[]
QED
