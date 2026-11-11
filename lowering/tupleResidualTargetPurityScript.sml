(* Diagnostic boundary: supported tuple targets do not require pure keys. *)
Theory tupleResidualTargetPurity
Ancestors
  supportedStmts supportedExprs vyperPureExpr

Theorem supported_subscript_internal_key_not_pure:
  supported_subscript_base tops nsid /\
  IS_SOME (supported_function_decl tops fid Internal) ==>
  supported_target tops bindings
    (SubscriptTarget (TopLevelNameTarget nsid)
      (Call (BaseT (UintT 256)) (IntCall fid) [] NONE)) /\
  ~pure_expr (Call (BaseT (UintT 256)) (IntCall fid) [] NONE)
Proof
  simp[supported_target_def, supported_expr_def, supported_effect_expr_def,
       supported_pure_expr_def, pure_expr_def]
QED
