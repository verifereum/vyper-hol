(* Memory case of the body induction for concat. *)
Theory bodyMemBiConcat
Ancestors
  bodyMemoryPreds bodyMemBiConcatFragments bodyMemBiConcatPrefix

Theorem body_builtin_concat_mem:
  !cx ty n es.
    (builtin_args_length_ok (Concat n) (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (Concat n) es)
Proof
  cheat
QED
