Theory bodyFullBopWordLayout
Ancestors
  exprSimOperators exprBopLowering exprLoweringProps
  gasShadowCompileStmtHelpers gasShadowState gasShadow
  bodySim exprSimHypsDefs fragExec exprSimSource compileEnv

Theorem bop_word_full_layout:
  word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1; e2]) sa = (op,sb) /\
  lower_value compile_expr cenv ty
    (gas_shadow_expr (Builtin ann (Bop bop) [e1; e2])) shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?x y s1 s2 shadow_s1 shadow_s2.
    lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
    lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) shadow_sa =
      (x,shadow_s1) /\
    lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e2) shadow_s1 =
      (y,shadow_s2) /\
    compile_binop bop x y (expr_type e1)
      (if bop = Exp then expr_int_literal e1 else NONE)
      (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
    gas_shadow_state s1 shadow_s1 /\ gas_shadow_state s2 shadow_s2 /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
    s2.cs_next_var <= sb.cs_next_var /\
    (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
    (!z. y = Var z ==> not_fresh_at s2 z) /\ (!l. y <> Label l) /\
    cs_extends shadow_sa shadow_s1 /\ cs_extends shadow_s1 shadow_s2 /\
    cs_extends shadow_s2 shadow_sb /\
    fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
    fn_has_code shadow_sa shadow_s1 shadow_func /\
    fn_has_code shadow_s1 shadow_s2 shadow_func /\
    fn_has_code shadow_s2 shadow_sb shadow_func
Proof
  strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `is_word_type (expr_type e1) /\ ~is_ArrayT (expr_type e1) /\
   ~is_bytestring_type (expr_type e1) /\
   is_word_type (expr_type e2) /\ ~is_ArrayT (expr_type e2) /\
   ~is_bytestring_type (expr_type e2)` by gvs[word_value_type_word] >>
  drule lower_value_bop >> simp[] >> strip_tac >>
  `expr_body_pre cenv cx env e2 es` by
    (first_assum irule >> gvs[expr_body_pre_def]) >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
    metis_tac[expr_body_pre_lower_value_word_shape] >>
  `cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
   (!z. y = Var z ==> not_fresh_at s2 z) /\ (!l. y <> Label l)` by
    metis_tac[expr_body_pre_lower_value_word_shape] >>
  drule compile_binop_shape >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def, gas_shadow_builtin_def, gas_shadow_expr_type] >> strip_tac >>
  drule lower_value_bop >> simp[gas_shadow_expr_type] >> strip_tac >>
  `x' = x /\ gas_shadow_state s1 s1'` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e1`, `e` |-> `e1`]
      gas_shadow_stmt_lower_value) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  `y' = y /\ gas_shadow_state s2 s2'` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e1`, `e` |-> `e2`]
      gas_shadow_stmt_lower_value) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s1`, `s1'`] mp_tac) >> simp[]) >>
  gvs[] >>
  `cs_extends shadow_sa s1' /\ cs_extends s1' s2'` by
    metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends s2' shadow_sb` by metis_tac[compile_binop_shape] >>
  metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl]
QED
