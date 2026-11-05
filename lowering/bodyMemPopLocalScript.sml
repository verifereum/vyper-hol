(* Memory case of the body induction, pop on a local dynamic array
   (bodyMemPopName's first disjunct; S1's compile_pop_name_case). *)
Theory bodyMemPopLocal
Ancestors
  bodyMemoryPreds

Theorem body_pop_local_mem:
  !cx ann id. body_expr_mem_ok cx (Pop ann (NameTarget id))
Proof
  cheat
QED
