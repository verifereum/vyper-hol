(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   assignment to a tuple target. *)
Theory bodyMemAssignTuple
Ancestors
  bodyMemoryPreds

Theorem body_assign_tuple_mem_case:
  !cx gs e.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_mem_ok cx (TupleTarget gs) v) /\ body_expr_mem_ok cx e ==>
    body_stmt_mem_ok cx (Assign (TupleTarget gs) e)
Proof
  cheat
QED
