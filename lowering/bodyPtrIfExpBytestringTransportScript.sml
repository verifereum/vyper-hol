Theory bodyPtrIfExpBytestringTransport
Ancestors
  bodyPtrIfExpSourceTyping bodyPtrIfExpMemoryTransport

Theorem ifexp_source_bytestring_ptr_mem_ok:
  !tops ctx ce cx env e es raw ee v er dst dv op G tn s.
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    eval_expr cx e es = (INL raw,ee) /\ read_result cx raw ee = (INL v,er) /\
    is_bytestring_type (lowered_value_type ce e) /\ is_bytestring_type dst /\
    evaluate_type (get_tenv cx) dst = SOME dv /\ value_has_type dv v /\
    ptr_mem_ok cx (lowered_value_type ce e) v op G tn s ==>
    ptr_mem_ok cx dst v op G tn s
Proof
  rpt strip_tac >>
  drule_all ifexp_source_lowered_typed >> strip_tac >>
  metis_tac[ptr_mem_ok_bytestring_transport]
QED
