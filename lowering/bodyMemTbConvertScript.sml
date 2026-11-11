(* Memory case of the body induction for convert (admitted; its own piece). *)
Theory bodyMemTbConvert
Ancestors
  bodyMemoryPreds

Theorem body_type_builtin_convert_mem_case:
  !cx v11 typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (Convert) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (TypeBuiltin v11 (Convert) typ es)
Proof
  cheat
QED
