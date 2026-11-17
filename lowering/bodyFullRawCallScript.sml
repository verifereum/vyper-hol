(* Raw calls over the shared finite-horizon expression judgments. *)
Theory bodyFullRawCall
Ancestors
  bodyFullPreds bodySimFull

Theorem raw_call_expr_full_ok:
  !cx ty flags es v18.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ty (RawCallTarget flags) es v18)
Proof
  cheat
QED
