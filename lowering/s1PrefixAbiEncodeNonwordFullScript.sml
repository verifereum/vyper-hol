(* Request-prefix companion to bodyFullAbiEncodeNonwordFull. *)
Theory s1PrefixAbiEncodeNonwordFull
Ancestors
  s1PrefixPreds bodyFullAbiEncodeNonwordFull s1PrefixDefs

Theorem abi_encode_nonword_vv_prefix_from_packaging:
  body_inv tops ctx ce cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  ~is_word_type (expr_type e) ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  cheat
QED
