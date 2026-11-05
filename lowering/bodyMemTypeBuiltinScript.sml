(* Memory case of the body induction (bodyMemory's body_mem_mutual): type
   builtins. *)
Theory bodyMemTypeBuiltin
Ancestors
  bodyMemoryPreds

Theorem body_type_builtin_mem_case:
  !cx v11 tb typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 tb typ es)
Proof
  cheat
QED
