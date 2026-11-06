(* Source action boundary for the dynamic extract32 memory case. *)
Theory bodyMemTbExtract32Action
Ancestors
  bodyMemoryPreds exprOpenFirstOperand exprSimSource exprSimHypsDefs
  vyperInterpreter vyperContext vyperTypeSystem vyperState vyperAST list
  allocLimits vyperTypeCallGraph vyperTypeCallStackSoundness supportedExprTraverse

Theorem extract32_eval_action:
  eval_expr cx (TypeBuiltin ann Extract32 ret [src;off]) =
  bind (bind (eval_expr cx src) (read_result cx)) (\v.
    bind (bind (eval_expr cx off) (read_result cx)) (\n.
      bind (lift_sum (evaluate_type_builtin cx Extract32 ret
        [expr_type src;expr_type off] [v;n])) (\r. return (Value r))))
Proof
  simp[Once evaluate_def, type_builtin_args_length_ok_def,
       type_check_def, vyperStateTheory.assert_def, ignore_bind_def, bind_return] >>
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  simp[bind_assoc, bind_return, FUN_EQ_THM] >>
  simp[Once bind_def, vyperStateTheory.assert_def]
QED

Theorem extract32_body_result_type:
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 ret [src;off]) es ==>
  ann = ret /\ ?bt. ret = BaseT bt /\ extract32_result_base_ok bt
Proof
  simp[expr_body_pre_def, well_typed_expr_def,
       type_builtin_result_ok_def, well_typed_type_builtin_args_def] >>
  metis_tac[]
QED

Theorem extract32_offset_body_pre:
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 ret [src;off]) es /\
  bind (eval_expr cx src) (read_result cx) es = (INL v,ee) ==>
  expr_body_pre cenv cx env off ee
Proof
  strip_tac >>
  `expr_body_pre cenv cx env src es` by
    (irule expr_body_pre_type_builtin_head >> metis_tac[]) >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.expr_body_pre_eval) >> strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def, byte_widths_expr_def,
      alloc_limits_expr_def, int_calls_expr_def,
      supportedExprTraverseTheory.supported_expr_exists_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm] >>
  metis_tac[call_evaluation_safe_append_right]
QED
