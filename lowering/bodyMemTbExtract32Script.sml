(* Memory case of the body induction for extract32 (admitted; its own piece). *)
Theory bodyMemTbExtract32
Ancestors
  bodyMemoryPreds

Theorem body_type_builtin_extract32_mem_case:
  !cx v11 typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (Extract32) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 (Extract32) typ es)
Proof
  cheat
QED
