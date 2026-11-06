Theory bodyPtrBytestringBuiltinsSemanticScreen
Ancestors
  bodySimExprCases bodyPtrBytestringBuiltinsOrderProbe

(* Semantic screening only: the inherited S1 interface supplies no
   pointer checks and does not certify the independent runtime fixture. *)
Theorem order_probe_body_expr_ok:
  !cx. body_expr_ok cx order_probe_expr
Proof
  gen_tac >> irule body_expr_ok_intro >>
  simp[order_probe_no_internal_calls]
QED
