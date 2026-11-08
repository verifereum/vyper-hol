(* Seam 2 joint induction, a family leaf of the agg step: array literals. *)
Theory bodyIntCallFamAggArray
Ancestors
  bodyIntCallJointContract

Theorem intcall_array_literal_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a t n args. e = Builtin a (MakeArray (SOME t) n) args) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
