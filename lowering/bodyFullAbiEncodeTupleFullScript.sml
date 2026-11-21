Theory bodyFullAbiEncodeTupleFull
Ancestors
  bodyFullAbiEncodeArgs bodyFullPreds bodySimFull exprSimHypsDefs
  vyperTypeSystem vyperState vyperAST list

Theorem abi_encode_tuple_vv_full_from_packaging:
  !tops ctx ce cx env ann ensure mid ty args es DF lo d shadow_ctx PG func shadow_func cty.
  body_inv tops ctx ce cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  (!s'' x t. type_check
      (type_builtin_args_length_ok (AbiEncode ensure mid) (LENGTH args))
      "TypeBuiltin args" s'' = (INL x,t) ==> body_exprs_full_ok cx args) ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx cty (TypeBuiltin ann (AbiEncode ensure mid) ty args) es
Proof
  rpt gen_tac >> strip_tac >>
  irule abi_encode_vv_full_from_packaging >> asm_simp_tac bool_ss [] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         qexists_tac `tops` >> asm_rewrite_tac[],
         qexists_tac `env` >> asm_rewrite_tac[]]
QED
