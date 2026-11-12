(* MethodId source composition keeps the forced value and value/place
   result domains distinct. *)
Theory bodyPtrEnvBuiltinsMethodSource
Ancestors bodyPtrEnvBuiltinsOperandCompose gasSummaryComposePtr
  exprSimHash exprSimDefs exprLowering vyperInterpreter vyperState
  gasExemptCert gasSummary fragGasPathPtr list vyperContext

Theorem method_id_source_action:
  eval_expr cx (Builtin ann MethodId [e]) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v es. ((case builtin_result cx es.accounts ann MethodId [expr_type e] [v] of
      INL w => INL (Value w) | INR exc => INR exc), es))
Proof
  irule eval_expr_unary_builtin_action >>
  simp[precompile_builtin_def, builtin_args_length_ok_def]
QED

Theorem method_id_marked_ptr_normal:
  gas_marked_exec_ptr D (ctx,fn) PG (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0) marks (INL v) ee G tn (OK t) /\
  builtin_result cx ee.accounts ann MethodId [expr_type e] [v] = INL r /\
  gas_path_ptr D 0 ctx fn PG G tn t 0 G' tn' (OK t') ==>
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx (Builtin ann MethodId [e]))
    (es,s0,G0,tn0) marks (INL (Value r)) ee G' tn' (OK t')
Proof
  strip_tac >> rewrite_tac[method_id_source_action] >>
  irule scalar_suffix_marked_compose >> goal_assum (drule_at Any) >>
  qexistsl_tac [`ee`, `v`] >> simp[]
QED

Theorem method_id_marked_ptr_exception:
  gas_marked_exec_ptr D (ctx,fn) PG (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0) marks (INR exc) ee G tn r ==>
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx (Builtin ann MethodId [e]))
    (es,s0,G0,tn0) marks (INR exc) ee G tn r
Proof
  strip_tac >> rewrite_tac[method_id_source_action] >>
  irule gas_marked_exec_ptr_bind_exception >> simp[]
QED

Theorem method_id_exempt:
  gas_exempt_cert F tops (ctx,fn)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s0) marks out endpoint ==>
  gas_exempt_cert F tops (ctx,fn)
    (ignore_bind (eval_expr cx (Builtin ann MethodId [e])) (return ()))
    (es,s0) marks out endpoint
Proof
  PairCases_on `out` >> PairCases_on `endpoint` >>
  strip_tac >> rewrite_tac[method_id_source_action, ignore_bind_def] >>
  once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED
