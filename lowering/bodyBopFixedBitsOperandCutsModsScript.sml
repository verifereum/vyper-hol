(* Physical operand cuts for strict fixed-bytes bit operations. *)
Theory bodyBopFixedBitsOperandCutsMods
Ancestors
  exprBopLowering exprWordOperand exprSimOperators exprLoweringProps
  gasShadowCompileStmtHelpers gasShadowState gasShadow
  exprSimFullBundleProps fragExec compileEnv vyperTypeSystem vyperAST list

Theorem fixed_bits_lower_cut[local]:
  lower_value compile_expr ce ty (Builtin ann (Bop bop) [e1;e2]) a = (out,b) /\
  MEM bop [And;Or;XOr;ShL;ShR] ==>
  ?x s1 y s2.
    lower_value compile_expr ce (expr_type e1) e1 a = (x,s1) /\
    lower_value compile_expr ce (expr_type e1) e2 s1 = (y,s2) /\
    compile_binop bop x y (expr_type e1) NONE NONE s2 = (out,b)
Proof
  strip_tac >>
  `bop <> In /\ bop <> NotIn /\ bop <> Eq /\ bop <> NotEq /\ bop <> Exp` by
    (qpat_assum `MEM bop _` mp_tac >> simp[] >> strip_tac >> gvs[]) >>
  drule lower_value_bop >> simp[]
QED

Theorem fixed_bits_shadow_operand[local]:
  gas_shadow_state a sha /\
  lower_value compile_expr cenv ty e a = (x,b) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (sx,shb) ==>
  x = sx /\ gas_shadow_state b shb
Proof
  strip_tac >>
  `gas_shadow_compiles (lower_value compile_expr cenv ty e)
      (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
    simp[gas_shadow_stmt_lower_value_env] >>
  qpat_x_assum `gas_shadow_compiles _ _` mp_tac >>
  simp[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`a`,`sha`] mp_tac) >> simp[]
QED

Theorem fixed_bits_has_code_cuts[local]:
  cs_extends a b /\ cs_extends b c /\ cs_extends c d /\ fn_has_code a d fn ==>
  fn_has_code a b fn /\ fn_has_code b c fn /\ fn_has_code c d fn
Proof
  strip_tac >>
  `cs_extends b d` by (irule cs_extends_trans >> qexists_tac `c` >> simp[]) >>
  `fn_has_code a b fn /\ fn_has_code b d fn` by metis_tac[fn_has_code_split] >>
  simp[] >> irule fn_has_code_split >> simp[]
QED

Theorem bop_fixed_bits_operand_cuts_mods:
  MEM bop [And;Or;XOr;ShL;ShR] /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  well_typed_expr env e1 /\ well_typed_expr env e2 /\
  (!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (out,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann (Bop bop) [e1;e2])) shadow_sa = (out,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) ==>
  ?x s1 y s2 sh1 sh2.
    lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e1) shadow_sa = (x,sh1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e2) sh1 = (y,sh2) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,s1,shadow_sa,sh1) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s1,s2,sh1,sh2) /\
    compile_binop bop x y (expr_type e1) NONE NONE s2 = (out,sb) /\
    fn_has_code s2 sb func /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\
    (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
    (!z. y = Var z ==> not_fresh_at s2 z)
Proof
  strip_tac >> drule_then strip_assume_tac expr_sim_full_code_fields >>
  qpat_x_assum `lower_value _ _ _ (Builtin _ _ _) _ = _`
    (mp_then Any (fn th => qpat_assum `MEM bop _` (mp_then Any mp_tac th))
      fixed_bits_lower_cut) >>
  disch_then (qx_choose_then `x` (qx_choose_then `s1`
    (qx_choose_then `y` (qx_choose_then `s2` strip_assume_tac)))) >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[SimpLHS,gas_shadow_expr_def,gas_shadow_builtin_def] >>
  disch_then (mp_then Any (fn th => qpat_assum `MEM bop _` (mp_then Any mp_tac th))
    fixed_bits_lower_cut) >>
  disch_then (qx_choose_then `sx` (qx_choose_then `sh1`
    (qx_choose_then `sy` (qx_choose_then `sh2` strip_assume_tac))) o
    REWRITE_RULE[gas_shadow_expr_type]) >>
  `x = sx /\ gas_shadow_state s1 sh1` by
    (irule fixed_bits_shadow_operand >> metis_tac[]) >>
  `y = sy /\ gas_shadow_state s2 sh2` by
    (irule fixed_bits_shadow_operand >> metis_tac[]) >>
  qpat_x_assum `x = sx` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `y = sy` (SUBST_ALL_TAC o SYM) >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
   (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
    metis_tac[lower_value_word_shape] >>
  `cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
   (!z. y = Var z ==> not_fresh_at s2 z)` by
    metis_tac[lower_value_word_shape] >>
  `cs_extends shadow_sa sh1 /\ cs_extends sh1 sh2` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends s2 sb /\ cs_extends sh2 shadow_sb` by metis_tac[compile_binop_shape] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    (irule fixed_bits_has_code_cuts >> simp[]) >>
  `fn_has_code shadow_sa sh1 shadow_func /\ fn_has_code sh1 sh2 shadow_func /\
   fn_has_code sh2 shadow_sb shadow_func` by
    (irule fixed_bits_has_code_cuts >> simp[]) >>
  qexistsl_tac [`sh1`,`sh2`] >> simp[expr_sim_full_code_def]
QED
