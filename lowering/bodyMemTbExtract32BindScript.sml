(* Actual two-operand source sequencing and memory-prefix transport. *)
Theory bodyMemTbExtract32Bind
Ancestors
  bodyMemTbExtract32Action bodyDeclMemoryCompose gasSummaryCompose
  gasExemptCert gasSummary gasOutcome vyperInterpreter vyperState list

Theorem extract32_marked_operands:
  gas_marked_exec T (ctx,func) (bind (eval_expr cx src) (read_result cx))
    (es,s0) left (INL v) mid (OK s1) /\
  gas_path_mem ctx func s1 0 (OK s2) /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx off) (read_result cx))
    (mid with gas_obs := [],s2) right (INL n) ee (OK s3) /\
  gas_marked_exec T (ctx,func)
    (bind (lift_sum (evaluate_type_builtin cx Extract32 ret
       [expr_type src;expr_type off] [v;n])) (\r. return (Value r)))
    (ee with gas_obs := [],s3) tail res fin r ==>
  gas_marked_exec T (ctx,func)
    (eval_expr cx (TypeBuiltin ann Extract32 ret [src;off]))
    (es,s0) (left ++ (right ++ tail)) res fin r
Proof
  strip_tac >> rewrite_tac[extract32_eval_action] >>
  irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >>
  irule gas_marked_exec_zero_prefix_mem >> goal_assum (drule_at Any) >>
  simp[] >> irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >> simp[]
QED

Theorem extract32_source_exception:
  gas_marked_exec T (ctx,func) (bind (eval_expr cx src) (read_result cx))
    (es,s0) marks (INR exc) fin r ==>
  gas_marked_exec T (ctx,func)
    (eval_expr cx (TypeBuiltin ann Extract32 ret [src;off]))
    (es,s0) marks (INR exc) fin r
Proof
  rewrite_tac[extract32_eval_action] >>
  metis_tac[gas_marked_exec_bind_exception]
QED

Theorem extract32_offset_exception:
  gas_marked_exec T (ctx,func) (bind (eval_expr cx src) (read_result cx))
    (es,s0) left (INL v) mid (OK s1) /\
  gas_path_mem ctx func s1 0 (OK s2) /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx off) (read_result cx))
    (mid with gas_obs := [],s2) right (INR exc) fin r ==>
  gas_marked_exec T (ctx,func)
    (eval_expr cx (TypeBuiltin ann Extract32 ret [src;off]))
    (es,s0) (left ++ right) (INR exc) fin r
Proof
  strip_tac >> rewrite_tac[extract32_eval_action] >>
  irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >>
  irule gas_marked_exec_zero_prefix_mem >> goal_assum (drule_at Any) >>
  simp[] >> irule gas_marked_exec_bind_exception >> simp[]
QED

Theorem extract32_source_exempt:
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind (bind (eval_expr cx src) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finish_state) ==>
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind (eval_expr cx (TypeBuiltin ann Extract32 ret [src;off])) (return ()))
    (es,s0) marks (err,ee) (leaf,finish_state)
Proof
  rewrite_tac[extract32_eval_action] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ignore_bind source (return ())` >>
  rewrite_tac[ignore_bind_def, bind_assoc] >> simp[] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem extract32_offset_exempt:
  gas_marked_exec T (ctx,func) (bind (eval_expr cx src) (read_result cx))
    (es,s0) left (INL v) mid (OK s1) /\
  gas_path_mem ctx func s1 0 (OK s2) /\
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind (bind (eval_expr cx off) (read_result cx)) (return ()))
    (mid with gas_obs := [],s2) right (err,ee) (leaf,finish_state) ==>
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind (eval_expr cx (TypeBuiltin ann Extract32 ret [src;off])) (return ()))
    (es,s0) (left ++ right) (err,ee) (leaf,finish_state)
Proof
  strip_tac >> rewrite_tac[extract32_eval_action] >>
  qmatch_asmsub_abbrev_tac `gas_marked_exec T _ source _ _ _ _ _` >>
  qmatch_asmsub_abbrev_tac `ignore_bind offset (return ())` >>
  rewrite_tac[ignore_bind_def, bind_assoc] >> simp[] >>
  irule gas_exempt_cert_bind_value >> goal_assum (drule_at Any) >>
  irule gas_exempt_cert_zero_prefix_mem >> goal_assum (drule_at Any) >>
  simp[bind_assoc] >> irule gas_exempt_cert_error_value >> simp[]
QED
