(* Request-prefix companion to bodyFullAbiDecodeExprConditional. *)
Theory s1PrefixAbiDecodeExprConditional
Ancestors
  s1PrefixPreds bodyFullAbiDecodeExprConditional s1PrefixDefs

Theorem abi_decode_singleton_vv_prefix:
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty0 (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es
Proof
  cheat
QED

Theorem abi_decode_expr_prefix:
  !cx v11 b typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (AbiDecode b) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) /\
    (!s'' x t.
       type_check (type_builtin_args_length_ok (AbiDecode b) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_prefix_ok cx es) ==>
    body_expr_prefix_ok cx (TypeBuiltin v11 (AbiDecode b) typ es)
Proof
  cheat
QED
