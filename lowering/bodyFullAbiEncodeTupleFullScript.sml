Theory bodyFullAbiEncodeTupleFull
Ancestors
  bodyFullAbiEncodeArgs bodyFullPreds bodySimFull exprSimHypsDefs
  vyperTypeSystem vyperState vyperAST list
  bodyFullPredsMods[qualified] bodyFullShadowBodyInv[qualified] bodyInvSplit[qualified]

Theorem abi_encode_tuple_vv_full_from_packaging:
  !mods exps tops ctx ce cx env ann ensure mid ty args es DF lo d shadow_ctx PG func shadow_func cty.
  (contract_inv mods exps ctx ce cx /\
     module_body_inv mods ce.ce_module tops ce cx) /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  (!s'' x t. type_check
      (type_builtin_args_length_ok (AbiEncode ensure mid) (LENGTH args))
      "TypeBuiltin args" s'' = (INL x,t) ==> body_exprs_full_ok_mods mods exps cx args) ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx cty (TypeBuiltin ann (AbiEncode ensure mid) ty args) es
Proof
  rpt gen_tac >> strip_tac >>
  irule abi_encode_vv_full_from_packaging >> simp[] >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `!s'' x t. type_check _ _ s'' = (INL x,t) ==> _`
      (drule_then ACCEPT_TAC)) >>
  qexistsl_tac [`env`, `tops`] >> asm_rewrite_tac[]
QED
