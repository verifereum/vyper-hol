(* Same-state precondition projection; this does not assert execution safety. *)
Theory bodyPtrSubscriptKeyPre
Ancestors
  exprSimHypsDefs allocLimits vyperTypeSystem vyperTypeCallStackSoundness
  supportedExprTraverse vyperTypeCallGraph list

Theorem expr_body_pre_nested_subscript_key:
  !cenv cx env ann inner base key idx es.
    expr_body_pre cenv cx env
      (Subscript ann (Subscript inner base key) idx) es ==>
    expr_body_pre cenv cx env key es
Proof
  simp[expr_body_pre_def, well_typed_expr_def, byte_widths_expr_def,
       alloc_limits_expr_def, int_calls_expr_def,
       supported_expr_exists_def, expr_has_evm_run_thm] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  metis_tac[call_evaluation_safe_append_left,
            call_evaluation_safe_append_right]
QED
