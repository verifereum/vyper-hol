Theory bodyMembershipFlagLayoutMods
Ancestors
  exprBopLowering exprLoweringProps exprOperandVar fragExec
  gasShadowCompileStmtHelpers gasShadowState gasShadow gasShadowCompile
  compileEnv vyperAST freshWrites

Theorem membership_flag_layout_mods:
  (bop = In \/ bop = NotIn) /\
  expr_type e1 = FlagT fid /\ expr_type e2 = FlagT fid /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann (Bop bop) [e1;e2])) sha = (op,shb) /\
  gas_shadow_state sa sha /\
  fn_has_code sa sb func /\ fn_has_code sha shb shadow_func ==>
  ?x s1 y s2 sh1 sh2.
    lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
    compile_binop bop x y (expr_type e1)
      (if bop = Exp then expr_int_literal e1 else NONE)
      (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
      (gas_shadow_expr e1) sha = (x,sh1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
      (gas_shadow_expr e2) sh1 = (y,sh2) /\
    compile_binop bop x y (expr_type e1)
      (if bop = Exp then expr_int_literal e1 else NONE)
      (if bop = Exp then expr_int_literal e2 else NONE) sh2 = (op,shb) /\
    gas_shadow_state s1 sh1 /\ gas_shadow_state s2 sh2 /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\
    cs_extends sha sh1 /\ cs_extends sh1 sh2 /\ cs_extends sh2 shb /\
    fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
    fn_has_code sha sh1 shadow_func /\ fn_has_code sh1 sh2 shadow_func /\
    fn_has_code sh2 shb shadow_func /\
    sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
    s1.cs_next_var <= s2.cs_next_var /\ s1.cs_next_id <= s2.cs_next_id /\
    s2.cs_next_var <= sb.cs_next_var /\ s2.cs_next_id <= sb.cs_next_id /\
    (local_ptrs_reserved cenv sa ==>
       (!z. x = Var z ==> not_fresh_at s1 z) /\
       (!z. y = Var z ==> not_fresh_at s2 z))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `bop <> Exp /\ bop <> Eq /\ bop <> NotEq` by
    (qpat_x_assum `bop = In \/ bop = NotIn` strip_assume_tac >> simp[]) >>
  qpat_x_assum `bop = In \/ bop = NotIn` kall_tac >>
  `~((bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type e2)) /\
   ~(is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq))` by
    simp[vyperASTTheory.is_ArrayT_def, is_bytestring_type_def] >>
  drule lower_value_bop >> simp[] >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def, gas_shadow_builtin_def] >>
  strip_tac >>
  qpat_x_assum `lower_value _ _ _ (Builtin _ _ _) _ = _` mp_tac >>
  strip_tac >>
  drule_at Any lower_value_bop >>
  simp[] >> strip_tac >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e1) e1)
      (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
        (gas_shadow_expr e1))` by irule gas_shadow_stmt_lower_value_env >>
  `x' = x /\ gas_shadow_state s1 s1'` by
    (qpat_x_assum `gas_shadow_compiles _ _` mp_tac >>
     simp[gas_shadow_compiles_def] >> disch_then drule >> simp[]) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e1) e2)
      (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
        (gas_shadow_expr e2))` by irule gas_shadow_stmt_lower_value_env >>
  `y' = y /\ gas_shadow_state s2 s2'` by
    (qpat_x_assum `gas_shadow_compiles _ (_ _ _ (gas_shadow_expr e2))` mp_tac >>
     simp[gas_shadow_compiles_def] >> disch_then drule >> simp[]) >>
  gvs[] >>
  imp_res_tac (cj 2 compile_expr_grows) >>
  imp_res_tac compile_binop_grows >>
  `cs_extends sa s2 /\ cs_extends s1 sb` by
    (conj_tac >> irule cs_extends_trans >- (qexists `s1` >> simp[]) >>
     qexists `s2` >> simp[]) >>
  `cs_extends sha s2' /\ cs_extends s1' shb` by
    (conj_tac >> irule cs_extends_trans >- (qexists `s1'` >> simp[]) >>
     qexists `s2'` >> simp[]) >>
  simp[] >> rpt conj_tac
  >- (irule fn_has_code_mid >> simp[] >> qexistsl [`sb`, `sa`] >> simp[cs_extends_refl])
  >- (irule fn_has_code_mid >> simp[] >> qexistsl [`sb`, `sa`] >> simp[])
  >- (irule fn_has_code_mid >> simp[] >> qexistsl [`sb`, `sa`] >> simp[cs_extends_refl])
  >- (irule fn_has_code_mid >> simp[] >> qexistsl [`shb`, `sha`] >> simp[cs_extends_refl])
  >- (irule fn_has_code_mid >> simp[] >> qexistsl [`shb`, `sha`] >> simp[])
  >- (irule fn_has_code_mid >> simp[] >> qexistsl [`shb`, `sha`] >> simp[cs_extends_refl])
  >> strip_tac >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  conj_tac >> metis_tac[compile_lower_value_var]
QED
