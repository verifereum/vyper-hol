(* Request-prefix lemmas for Env reads, CalldataLen, bad arity, literal MethodId and type bounds. *)
Theory s1PrefixBuiltinLeaves
Ancestors
  s1PrefixFrame s1PrefixDefs exprSimCalldata exprSimHash exprBodyPreProps
  vyperStorageTrace vyperTypeBuiltins vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperAST list

Triviality env_read_eval_state:
  item <> MsgGas /\ eval_expr cx (Builtin ann (Env item) []) st = (res, st') ==>
  st' = st
Proof
  simp[Once evaluate_def, builtin_args_length_ok_def] >> strip_tac >>
  gvs[type_check_def, assert_def, bind_def, ignore_bind_def, return_def,
      get_accounts_def] >>
  gvs[Once evaluate_def, bind_def, return_def, get_accounts_def] >>
  Cases_on `evaluate_builtin cx st.accounts ann (Env item) [] []` >>
  gvs[lift_sum_def, bind_def, return_def, raise_def,
      is_self_codesize_def]
QED

Theorem env_item_sim_prefix:
  item <> MsgGas /\ builtin_args_length_ok (Env item) (LENGTH args) ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin ann (Env item) args) es /\
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin ann (Env item) args) es
Proof
  strip_tac >> gvs[builtin_args_length_ok_def] >>
  rw[expr_sim_prefix_def, expr_sim_full_pre_def,
     expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >>
  rpt gen_tac >>
  namedCases_on `eval_expr cx (Builtin ann (Env item) []) (es with gas_obs := gobs)`
    ["env_result eval_state"] >>
  drule_all_then SUBST_ALL_TAC env_read_eval_state >>
  Cases_on `env_result` >> simp[bind_def] >> rw[] >> simp[] >>
  drule_then SUBST_ALL_TAC read_result_state >> simp[]
QED

Theorem calldatalen_sim_prefix:
  builtin_args_length_ok CalldataLen (LENGTH args) ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin ann CalldataLen args) es /\
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin ann CalldataLen args) es
Proof
  strip_tac >> gvs[builtin_args_length_ok_def] >>
  rw[expr_sim_prefix_def, expr_sim_full_pre_def,
     expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >>
  rpt gen_tac >>
  Cases_on `eval_expr cx (Builtin ann CalldataLen []) (es with gas_obs := gobs)` >>
  drule eval_expr_calldata_len >> strip_tac >>
  gvs[bind_def, read_result_def, return_def] >> rw[] >> simp[]
QED

Theorem builtin_bad_arity_sim_prefix:
  ~builtin_args_length_ok bt (LENGTH args) ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin ann bt args) es /\
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin ann bt args) es
Proof
  rw[expr_sim_prefix_def, expr_sim_full_pre_def,
     expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, Once evaluate_def, type_check_def,
       assert_def, bind_def, ignore_bind_def, raise_def]
QED

Theorem method_id_literal_sim_prefix:
  method_id_literal (Literal la l) = SOME bs ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin ann MethodId [Literal la l]) es /\
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin ann MethodId [Literal la l]) es
Proof
  rw[expr_sim_prefix_def, expr_sim_full_pre_def,
     expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >>
  rpt gen_tac >>
  Cases_on `eval_expr cx (Builtin ann MethodId [Literal la l])
    (es with gas_obs := gobs)` >>
  drule_all eval_expr_method_id_literal >> strip_tac >>
  gvs[bind_def, read_result_def, return_def] >> rw[] >> simp[]
QED

Theorem bound_builtin_sim_prefix:
  MEM tb [MaxValue; MinValue; Epsilon] /\
  expr_body_pre cenv cx env (TypeBuiltin ann tb typ args) es ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (TypeBuiltin ann tb typ args) es /\
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (TypeBuiltin ann tb typ args) es
Proof
  strip_tac >> drule expr_body_pre_static_facts >> strip_tac >>
  `args = []` by
    (fs[well_typed_expr_def] >>
     drule well_typed_type_builtin_args_length >>
     gvs[type_builtin_args_length_ok_def]) >>
  gvs[] >>
  rw[expr_sim_prefix_def, expr_sim_full_pre_def,
     expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, Once evaluate_def, type_builtin_args_length_ok_def,
       type_check_def, assert_def, bind_def, ignore_bind_def, return_def, raise_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  rpt gen_tac >>
  qmatch_goalsub_rename_tac `lift_sum (evaluate_type_builtin cx kind typ [] [])` >>
  Cases_on `evaluate_type_builtin cx kind typ [] []` >>
  simp[lift_sum_def, bind_def, return_def, raise_def, read_result_def] >>
  rw[] >> simp[]
QED
