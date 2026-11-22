(* Request-prefix companion to bodyFullTypeBuiltinExtract32. *)
Theory s1PrefixTypeBuiltinExtract32
Ancestors
  s1PrefixPreds bodyFullTypeBuiltinExtract32

Theorem extract32_expr_prefix_ok:
  !cx v11 typ es.
  (!s'' x t.
       type_check (type_builtin_args_length_ok Extract32 (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) /\
  (!s'' x t.
       type_check (type_builtin_args_length_ok Extract32 (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (TypeBuiltin v11 Extract32 typ es)
Proof
  cheat
QED
