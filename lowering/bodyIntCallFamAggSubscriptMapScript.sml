(* Seam 2 joint induction, a frozen leaf of the subscript step: the
   mapping-place producer for a Subscript (the target's second conjunct).
   FROZEN OWNER LEAF: proved by its own run, cheat until then. *)
Theory bodyIntCallFamAggSubscriptMap
Ancestors
  bodyIntCallJointContract

Theorem intcall_subscript_map_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a base idx. e = Subscript a base idx) ==>
  intcall_map_producer fp e
Proof
  cheat
QED
