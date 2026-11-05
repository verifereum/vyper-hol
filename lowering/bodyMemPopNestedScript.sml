(* Memory case of the body induction (bodyMemory's body_mem_mutual): pop on a
   nested target. *)
Theory bodyMemPopNested
Ancestors
  bodyMemoryPreds

Theorem body_pop_nested_mem_case:
  !cx v10 bt.
    (!id. bt <> NameTarget id) /\ (!nid. bt <> TopLevelNameTarget nid) /\
    body_base_target_mem_ok cx bt ==>
    body_expr_mem_ok cx (Pop v10 bt)
Proof
  cheat
QED
