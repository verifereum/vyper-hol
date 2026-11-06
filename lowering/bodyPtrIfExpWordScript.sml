Theory bodyPtrIfExpWord
Ancestors
  bodyPtrDefs bodyPtrPreds exprPtrUnwrap exprSimIfExp exprSimOperators
  bodyPtrIfExpAssignFrame ifJumpPtr gasSummaryComposePtr exprLowering
  vyperAST vyperInterpreter vyperState

Theorem word_probe_eval_forced[local]:
  eval_expr cx (IfExp t c a b) =
  bind (bind (eval_expr cx c) (read_result cx))
    (\v. if v = BoolV T then bind (eval_expr cx a) (conditional_result cx)
         else if v = BoolV F then bind (eval_expr cx b) (conditional_result cx)
         else raise (Error (TypeError "not BoolV")))
Proof
  simp[Once evaluate_def, switch_BoolV_def, vyperStateTheory.bind_assoc] >>
  simp[FUN_EQ_THM, vyperStateTheory.bind_def] >> gen_tac >>
  Cases_on `eval_expr cx c x` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `read_result cx captured st` >>
  Cases_on `read_result cx captured st` >> rename1 `_ = (forced,sf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >>
  simp[raise_def, vyperStateTheory.bind_def]
QED

