Theory bodyFullAbiEncodeNonwordFull
Ancestors
  bodyFullAbiEncodeArgs bodyFullPreds bodySimFull
  exprSimHyps exprSimHypsDefs exprSimAbiEncodeRuntimeInputs aggregateEvaluatedLayout
  vyperState vyperAST list
  bodyFullPredsMods[qualified] bodyFullShadowBodyInv[qualified] bodyInvSplit[qualified]

Theorem abi_encode_nonword_vv_full_from_packaging:
  (contract_inv mods exps ctx ce cx /\
     module_body_inv mods ce.ce_module tops ce cx) /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  body_expr_full_ok_mods mods exps cx e /\ ~is_word_type (expr_type e)
  ==> expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  strip_tac >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[expr_body_pre_lowered_fits, arg_type_fits_word_type] >>
  `body_exprs_full_ok cx [e]` by simp[body_exprs_full_ok_def] >>
  irule abi_encode_vv_full_from_packaging >> simp[] >>
  qexistsl_tac [`env`, `tops`] >> asm_rewrite_tac[]
QED
