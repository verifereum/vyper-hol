(* Seam 2 joint induction, a family leaf of the agg step: struct literals. *)
Theory bodyIntCallFamAggStruct
Ancestors
  bodyIntCallJointContract bodyIntCallFamAggStructFields
  bodyIntCallFamAggStructSource bodyIntCallFamAggStructCode

Theorem intcall_struct_literal_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a nm fields. e = StructLit a nm fields) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
