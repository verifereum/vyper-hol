(* Seam 2 joint induction, a family leaf of the agg step: tuple literals. *)
Theory bodyIntCallFamAggTuple
Ancestors
  bodyIntCallJointContract

Theorem intcall_tuple_literal_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a n args. e = Builtin a (MakeArray NONE n) args) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
