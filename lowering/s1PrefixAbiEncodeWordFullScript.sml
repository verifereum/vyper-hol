(* Request-prefix companion to bodyFullAbiEncodeWordFull. *)
Theory s1PrefixAbiEncodeWordFull
Ancestors
  s1PrefixPreds bodyFullAbiEncodeWordFull s1PrefixDefs

Theorem abi_encode_word_vv_prefix_from_packaging:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\
  is_word_type (expr_type e) ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  cheat
QED
