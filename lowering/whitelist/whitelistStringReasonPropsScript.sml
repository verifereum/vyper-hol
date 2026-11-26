Theory whitelistStringReasonProps
Ancestors
  vyperAST supportedExprs supportedStmts

Theorem supported_string_reason_from_pure:
  supported_pure_expr tops e /\ expr_type e = BaseT (StringT n) ==>
  supported_string_reason tops e
Proof
  Cases_on `e` >> gvs[supported_string_reason_def, expr_type_def] >>
  rename1 `Literal _ l` >> Cases_on `l` >>
  simp[supported_string_reason_def, expr_type_def, GSYM AND_IMP_INTRO] >>
  rpt strip_tac >> gvs[]
QED
