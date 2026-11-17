Theory bodyFullBopBytesEqLayout
Ancestors
  exprBopLowering gasShadowCompileStmtHelpers gasShadowState gasShadow
  exprLowering compileEnv vyperAST

Theorem bop_bytes_eq_layout:
  (bop = Eq \/ bop = NotEq) /\
  (expr_type e1 = BaseT AddressT \/
   ?m. expr_type e1 = BaseT (BytesT (Fixed m))) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  lower_value compile_expr cenv ty
    (gas_shadow_expr (Builtin ann (Bop bop) [e1;e2])) sha = (op,shb) /\
  gas_shadow_state sa sha ==>
  ?x s1 y s2 sh1 sh2.
    lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
    compile_binop bop x y (expr_type e1) NONE NONE s2 = (op,sb) /\
    lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) sha = (x,sh1) /\
    lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e2) sh1 = (y,sh2) /\
    compile_binop bop x y (expr_type e1) NONE NONE sh2 = (op,shb) /\
    gas_shadow_state s1 sh1 /\ gas_shadow_state s2 sh2
Proof
  strip_tac >>
  `bop <> In /\ bop <> NotIn /\ bop <> Exp /\
   ~is_bytestring_type (expr_type e1)` by
    (rpt strip_tac >> gvs[is_bytestring_type_def]) >>
  drule lower_value_bop >> simp[] >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def, gas_shadow_builtin_def] >> strip_tac >>
  drule lower_value_bop >> simp[is_bytestring_type_def] >> strip_tac >>
  mp_tac (Q.INST [`ty` |-> `expr_type e1`, `e` |-> `e1`]
    gas_shadow_stmt_lower_value) >>
  simp[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sa`, `sha`] mp_tac) >> gvs[] >> strip_tac >> gvs[] >>
  mp_tac (Q.INST [`ty` |-> `expr_type e1`, `e` |-> `e2`]
    gas_shadow_stmt_lower_value) >>
  simp[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`s1`, `s1'`] mp_tac) >> gvs[]
QED
