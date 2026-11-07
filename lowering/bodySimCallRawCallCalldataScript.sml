(* Piece of bodySimCallCases.body_raw_call_calldata_case. *)

Theory bodySimCallRawCallCalldata
Ancestors
  bodySimExprCases exprSimRawCallCalldata
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph

(* exprSimRawCallCalldata's compile_raw_call_calldata_case, over operands
   that may contain internal calls. *)
Theorem raw_call_calldata_body_expr_ok:
  !cx ty flags es v19.
    body_exprs_ok cx es ==>
    body_expr_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  rpt strip_tac >> irule body_expr_ok_of_case >> conj_tac >~ [`_ <> Subscript _ _ _`] >- simp[] >> rpt strip_tac >>
  `exprs_case F ctx func cenv cx es` by metis_tac[body_exprs_ok_case] >>
  simp[compile_raw_call_calldata_case]
QED
