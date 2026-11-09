Theory abiEncodeArgsCase
Ancestors
  abiEncodeArgsSim exprSimHyps exprSimSource exprSimHypsDefs vyperTypeInvariants
  vyperTypeSystem compileEnv arithmetic

Theorem abi_args_fits_memory_bytes:
  (!t u. arg_type_fits t u ==>
    type_memory_bytes ce t <= type_memory_bytes ce u) /\
  (!ts us. arg_types_fit ts us ==>
    SUM (MAP (type_memory_bytes ce) ts) <=
    SUM (MAP (type_memory_bytes ce) us))
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  simp[arg_type_fits_def, type_memory_bytes_def] >> rpt strip_tac >>
  gvs[]
  >- (irule DIV_LE_MONOTONE >> simp[])
  >- (irule DIV_LE_MONOTONE >> simp[])
  >- (irule LESS_MONO_MULT2 >> simp[]) >>
  metis_tac[LESS_MONO_MULT2]
QED

Theorem abi_args_success_ready:
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  expr_sim_inv ce cx env es' /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
         value_has_type tv v /\ val_wf tv v /\
         type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
         type_memory_size tv < 2 ** 64 /\
         type_memory_size tv + 64 < dimword (:256))
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es'` by metis_tac[expr_body_pre_eval] >>
  `MAP FDOM es.scopes = MAP FDOM es'.scopes` by
    (drule exprSimSourceTheory.eval_expr_read_INL >> strip_tac >>
     `es' = t` by metis_tac[vyperStateTheory.read_result_state] >> gvs[] >>
     metis_tac[vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom]) >>
  simp[] >> strip_tac >>
  drule_all memory_rhs_read_lowered_typed_unwidened >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >> strip_tac >>
  qexists `tv` >> simp[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >> simp[] >>
  `type_memory_bytes ce (lowered_value_type ce e) <=
     type_memory_bytes ce (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits, abi_args_fits_memory_bytes] >>
  `type_memory_bytes ce (expr_type e) < 2 ** 64` by
    (gvs[expr_body_pre_def] >>
     drule alloc_limits_expr_type_alloc_ok >>
     simp[allocLimitsTheory.type_alloc_ok_def]) >>
  gvs[wordsTheory.dimword_def] >> decide_tac
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
     byte_widths_expr_def, allocLimitsTheory.alloc_limits_expr_def,
     supportedExprTraverseTheory.supported_expr_exists_def,
     supportedExprTraverseTheory.supported_exprs_exists_every, listTheory.EXISTS_MEM] >>
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
  qexists `nocalls` >> simp[listTheory.EVERY_MEM] >> rpt strip_tac
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
  cheat
QED
