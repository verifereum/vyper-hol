(* Piece of bodySimCallCases.body_raw_call_case. *)

Theory bodySimCallRawCall
Ancestors
  bodySimExprCases exprSimRawCall
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph

(* exprSimRawCall's compile_raw_call_case at nocalls = F. *)
Theorem raw_call_body_expr_ok:
  !cx ty flags es v18.
    body_exprs_ok cx es ==>
    body_expr_ok cx (Call ty (RawCallTarget flags) es v18)
Proof
  rpt strip_tac >> irule body_expr_ok_of_case >>
  conj_tac >- gvs[] >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >> rpt strip_tac >>
  `exprs_case F ctx func cenv cx es` by metis_tac[body_exprs_ok_case] >>
  simp[compile_raw_call_case]
QED
