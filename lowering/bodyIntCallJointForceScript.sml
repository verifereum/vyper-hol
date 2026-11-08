(* Seam 2 joint induction step: the forced-value producer from the value producer. *)
Theory bodyIntCallJointForce
Ancestors
  bodyIntCallJointContract

(* L-force: the forced-value sibling of any expression from its value
   producer, by protected_value_forcing at the value's endpoint. *)
Theorem intcall_forced_producer_from_value:
  intcall_expr_producer fp e ==> intcall_forced_producer fp e
Proof
  cheat
QED
