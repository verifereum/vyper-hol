(* Memory case of the body induction, pop on a module variable
   (bodyMemPopName's second disjunct; S1's compile_pop_storage_sim, with
   immutables excluded by typing as in compile_pop_immutable_sim). *)
Theory bodyMemPopToplevel
Ancestors
  bodyMemoryPreds

Theorem body_pop_toplevel_mem:
  !cx ann nid. body_expr_mem_ok cx (Pop ann (TopLevelNameTarget nid))
Proof
  cheat
QED
