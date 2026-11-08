(* Seam 2 joint induction, a family leaf of the agg step: subscripts (every place_type case). *)
Theory bodyIntCallFamAggSubscript
Ancestors
  bodyIntCallJointContract

Theorem intcall_subscript_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a base idx. e = Subscript a base idx) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
