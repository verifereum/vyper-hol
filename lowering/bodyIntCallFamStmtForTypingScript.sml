(* Static body-typing boundary for all For iterators. *)
Theory bodyIntCallFamStmtForTyping
Ancestors vyperTypeSystem

Theorem singleton_for_body_typing:
  IS_SOME (type_stmts env ret [For id ty it bound body]) ==>
  IS_SOME (type_stmts (extend_local env id ty F) ret body)
Proof
  simp[Once type_stmt_def] >>
  Cases_on `type_stmt env ret (For id ty it bound body)` >>
  simp[Once type_stmt_def] >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp[Once type_stmt_def] >>
  IF_CASES_TAC >> simp[]
QED
