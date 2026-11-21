(*
 * raw_call with calldata over the finite-horizon joint judgment.
 * Its lowering emits a DALLOCA into the function.
 *
 * TOP-LEVEL:
 *   raw_call_calldata_expr_full_ok -- the raw_call-with-calldata case
 *)
Theory bodyFullRawCallCalldata
Ancestors
  bodyFullPreds bodySimFull rawCallCalldataDalloca exprSimHypsDefs fragExec
  ptrDiscipline exprLowering vyperTypeSystem vyperAST list

val _ = Parse.hide "body";

(* GATE_ADMISSION: missing case, raw_call with msg.data body simulation; owner: dalloca sweep *)
Theorem raw_call_calldata_expr_full_ok:
  !cx ty flags es v19.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  cheat
QED
