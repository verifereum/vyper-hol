Theory abiEncodeArgsCase
Ancestors
  abiEncodeArgsSim exprSimHyps vyperTypeInvariants

Theorem abi_args_success_ready:
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  expr_sim_inv ce cx env es' /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         value_has_type tv v /\ val_wf tv v /\
         type_memory_bytes ce (expr_type e) = type_memory_size tv /\
         type_memory_size tv < 2 ** 64 /\
         type_memory_size tv + 64 < dimword (:256))
Proof
  rpt strip_tac >>
  drule_all expr_body_pre_eval >> strip_tac
  >- (drule eval_expr_read_INL >> strip_tac >>
      `es' = t` by metis_tac[vyperStateTheory.read_result_state] >> gvs[] >>
      drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[vyperTypeExprResultTheory.expr_result_typed_def,
      vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
      vyperTypeInvariantsTheory.value_result_typed_def] >>
  drule_all expr_body_pre_copy_ok >> strip_tac >>
  goal_assum (drule_at Any) >>
  simp[valueEncodingTypingTheory.value_has_type_val_wf, abi_args_capture_size] >>
  gvs[]
QED

Theorem abi_args_ready_cases:
  !args.
  exprs_case nocalls ctx func ce cx args /\
  EVERY (\e. !es. expr_sim_inv ce cx env es ==>
    expr_body_pre ce cx env e es /\ (nocalls ==> int_calls_expr e = [])) args ==>
  abi_args_ready ctx func ce cx (expr_sim_inv ce cx env) args
Proof
  Induct >> simp[exprs_case_def, abi_args_ready_def] >> rpt strip_tac
  >- (gvs[expr_sim_case_def] >> metis_tac[])
  >- (gvs[expr_vv_case_def] >> metis_tac[])
  >- metis_tac[expr_body_pre_res_ok]
  >- metis_tac[abi_args_success_ready]
  >- metis_tac[abi_args_success_ready]
  >- (`expr_body_pre ce cx env h es` by metis_tac[] >>
      drule_all abi_args_success_ready >> simp[]) >>
  metis_tac[]
QED

Theorem abi_args_body_pre_arg:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  MEM e args /\ expr_sim_inv ce cx env es' ==>
  expr_body_pre ce cx env e es'
Proof
  rw[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
     vyperTypeCallGraphTheory.int_calls_expr_def,
     byte_widths_expr_def, allocLimitsTheory.alloc_limits_expr_def] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
QED

Theorem abi_args_ready_case:
  exprs_case nocalls ctx func ce cx args /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  (nocalls ==> int_calls_expr (TypeBuiltin ann (AbiEncode ensure mid) ty args) = []) ==>
  abi_args_ready ctx func ce cx (expr_sim_inv ce cx env) args
Proof
  strip_tac >> irule abi_args_ready_cases >>
  qexists_tac `nocalls` >> simp[listTheory.EVERY_MEM] >> rpt strip_tac
  >- (irule abi_args_body_pre_arg >> metis_tac[]) >>
  gvs[vyperTypeCallGraphTheory.int_calls_expr_def] >>
  metis_tac[int_calls_exprs_mem]
QED

Theorem compile_abi_encode_args_case_sim:
  exprs_case nocalls ctx func ce cx args /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  (nocalls ==> int_calls_expr (TypeBuiltin ann (AbiEncode ensure mid) ty args) = []) /\
  compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
  eval_exprs cx args es = (rr,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s)
    (wb_args_exit rr)
Proof
  strip_tac >> drule_all abi_args_ready_case >> strip_tac >>
  irule compile_abi_encode_args_sim >> simp[] >>
  qexistsl [`expr_sim_inv ce cx env`, `env`] >>
  gvs[expr_body_pre_def]
QED
