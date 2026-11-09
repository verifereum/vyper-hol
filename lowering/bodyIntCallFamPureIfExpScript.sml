(* Seam 2 joint induction, a family leaf of the pure step: ternaries. *)
Theory bodyIntCallFamPureIfExp
Ancestors
  bodyIntCallJointContract

Theorem intcall_ifexp_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?ty c e1 e2. e = IfExp ty c e1 e2) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
