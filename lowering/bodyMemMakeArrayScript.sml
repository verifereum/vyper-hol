(* Memory case of the body induction (bodyMemory's body_mem_mutual): array
   literal. *)
Theory bodyMemMakeArray
Ancestors
  bodyMemoryPreds

Theorem body_make_array_mem_case:
  !cx ty t n es.
    (builtin_args_length_ok (MakeArray t n) (LENGTH es) ==>
     body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (MakeArray t n) es)
Proof
  cheat
QED
