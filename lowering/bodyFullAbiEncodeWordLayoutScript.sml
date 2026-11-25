Theory bodyFullAbiEncodeWordLayout
Ancestors
  bodySim exprSimSource exprSimHyps exprSimAbiEncodeRuntimeInputs
  exprSimAbiEncodePrefixWindow vyperTypeArgFits exprReasonOperand
  gasShadowCompileStmtHelpers gasShadowCompilePure gasShadowCompileBase
  gasShadowState exprLoweringProps abiBuiltinEncodeWord exprBopLowering
  exprLowering compileEnv fragExec vyperAST list pair

Theorem abi_word_compile_at[local]:
  lowered_value_type ce e = expr_type e /\ is_word_type (expr_type e) /\
  reason_result_shape (expr_type e) loc (FST (compile_expr ce (expr_type e) e sa)) /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) ==>
  compile_expr ce cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) sa =
    as_ptr_val ann LocMemory
      (lower_abi_encode (OPTION_MAP bytes_method_id_word mid) 32
        (\dst. comp_ignore_bind (emit_void MSTORE [dst;op]) (comp_return (Lit 32w))) sm)
Proof
  strip_tac >> drule_all compile_abi_encode_word_direct >>
  simp[abi_encode_word_size_bound]
QED

Theorem abi_word_pack_mono[local]:
  ci_mono sm (SND (lower_abi_encode meth 32
    (\dst. comp_ignore_bind (emit_void MSTORE [dst;op]) (comp_return (Lit 32w))) sm))
Proof
  irule ci_mono_lower_abi_encode >>
  simp[ci_mono_ignore_bind, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem abi_encode_word_child_layout:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  is_word_type (expr_type e) /\
  compile_expr ce cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) cty
    (gas_shadow_expr (TypeBuiltin ann (AbiEncode F mid) ty [e])) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?op sm shadow_sm out.
    lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (op,shadow_sm) /\
    gas_shadow_state sm shadow_sm /\
    gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
    fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
    expr_body_pre ce cx env e es /\
    lowered_value_type ce e = expr_type e /\
    abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) = 32 /\
    lower_abi_encode (OPTION_MAP bytes_method_id_word mid) 32
      (\dst. comp_ignore_bind (emit_void MSTORE [dst;op]) (comp_return (Lit 32w))) sm = (out,sb) /\
    lower_abi_encode (OPTION_MAP bytes_method_id_word mid) 32
      (\dst. comp_ignore_bind (emit_void MSTORE [dst;op]) (comp_return (Lit 32w))) shadow_sm = (out,shadow_sb) /\
    vv = LocatedValue ann (mk_ptr out LocMemory) /\
    fn_has_code sm sb func /\ fn_has_code shadow_sm shadow_sb shadow_func /\
    ci_mono sa sm /\ ci_mono sm sb /\
    ci_mono shadow_sa shadow_sm /\ ci_mono shadow_sm shadow_sb
Proof
  strip_tac >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  `lowered_value_type ce e = expr_type e` by
    metis_tac[expr_body_pre_lowered_fits, arg_type_fits_prim_word,
              membership_element_word_boundary] >>
  `reason_uniform_shape compile_expr ce (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >>
     fs[exprSimHypsDefsTheory.expr_body_pre_def, exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  `?loc. reason_result_shape (expr_type e) loc (FST (compile_expr ce (expr_type e) e sa))` by
    (qpat_x_assum `reason_uniform_shape _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [reason_uniform_shape_def]) >>
     qexists_tac `loc` >> Cases_on `compile_expr ce (expr_type e) e sa` >>
     metis_tac[pairTheory.FST]) >>
  Cases_on `lower_value compile_expr ce (expr_type e) e sa` >>
  rename1 `lower_value _ _ _ e sa = (op,sm)` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
    (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (shop,shadow_sm)` >>
  `gas_shadow_compiles (lower_value compile_expr ce (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e))` by
    irule gas_shadow_stmt_lower_value_env >>
  `shop = op /\ gas_shadow_state sm shadow_sm` by
    (pop_assum (qspecl_then [`sa`, `shadow_sa`] mp_tac o
                REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  qpat_x_assum `shop = op` SUBST_ALL_TAC >>
  `gas_shadow_compiles (compile_expr ce (expr_type e) e)
     (compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e))` by
    irule gas_shadow_stmt_compile_expr_env >>
  `FST (compile_expr ce (expr_type e) e sa) =
   FST (compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_sa)` by
    (pop_assum (qspecl_then [`sa`, `shadow_sa`] mp_tac o
                REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  `reason_result_shape (expr_type e) loc
      (FST (compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_sa))` by
    (qpat_x_assum `FST (compile_expr ce (expr_type e) e sa) = _`
       (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `meth = OPTION_MAP bytes_method_id_word mid` >>
  qabbrev_tac `encode = \dst. comp_ignore_bind
    (emit_void MSTORE [dst;op]) (comp_return (Lit 32w))` >>
  `compile_expr ce cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) sa =
     as_ptr_val ann LocMemory (lower_abi_encode meth 32 encode sm)` by
    (qunabbrev_tac `meth` >> qunabbrev_tac `encode` >> drule_all abi_word_compile_at >>
     disch_then (fn th => pure_rewrite_tac[th]) >> REFL_TAC) >>
  `compile_expr (gas_shadow_env T ce) cty
      (gas_shadow_expr (TypeBuiltin ann (AbiEncode F mid) ty [e])) shadow_sa =
     as_ptr_val ann LocMemory (lower_abi_encode meth 32 encode shadow_sm)` by
    (drule_all (SIMP_RULE (srw_ss())
       [gasShadowTheory.gas_shadow_expr_type, gas_shadow_lowered_value_type]
       (Q.INST [`ce` |-> `gas_shadow_env T ce`, `e` |-> `gas_shadow_expr e`]
          abi_word_compile_at)) >>
     disch_then (fn th => simp[NoAsms, th, gasShadowTheory.gas_shadow_expr_def,
                                Abbr `meth`, Abbr `encode`])) >>
  `ci_mono sm (SND (lower_abi_encode meth 32 encode sm)) /\
   ci_mono shadow_sm (SND (lower_abi_encode meth 32 encode shadow_sm))` by
    simp[Abbr `encode`, abi_word_pack_mono] >>
  Cases_on `lower_abi_encode meth 32 encode sm` >>
  Cases_on `lower_abi_encode meth 32 encode shadow_sm` >>
  fs[as_ptr_val_def] >>
  qpat_x_assum `_ = sb` SUBST_ALL_TAC >>
  qpat_x_assum `_ = shadow_sb` SUBST_ALL_TAC >>
  rename1 `lower_abi_encode meth 32 encode sm = (out,sb)` >>
  rename1 `lower_abi_encode meth 32 encode shadow_sm = (shadow_out,shadow_sb)` >>
  `shadow_out = out` by
    (qpat_x_assum `LocatedValue ann (mk_ptr shadow_out LocMemory) = vv` mp_tac >>
     qpat_x_assum `LocatedValue ann (mk_ptr out LocMemory) = vv` (SUBST1_TAC o SYM) >>
     simp[contextTheory.mk_ptr_def]) >>
  qpat_x_assum `shadow_out = out` SUBST_ALL_TAC >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by
    metis_tac[ci_mono_lower_value_compile_expr, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sb shadow_func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  simp[abi_encode_word_size_bound] >>
  irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)
QED
