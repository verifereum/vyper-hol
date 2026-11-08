(* Seam 2 joint induction, a family leaf of the agg step: attributes. *)
Theory bodyIntCallFamAggAttribute
Ancestors
  bodyIntCallJointContract

Theorem intcall_attribute_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a base fld. e = Attribute a base fld) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
