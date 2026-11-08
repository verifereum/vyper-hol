(* Seam 2 joint induction, a family leaf of the call step: pops. *)
Theory bodyIntCallFamCallPop
Ancestors
  bodyIntCallJointContract

Theorem intcall_pop_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a tgt. e = Pop a tgt) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
