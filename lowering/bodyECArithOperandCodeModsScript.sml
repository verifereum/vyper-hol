(* Real and shadow compiler cuts for the two strict EC arithmetic operands. *)
Theory bodyECArithOperandCodeMods
Ancestors
  exprSimECArith exprSimFullBundleProps exprLoweringProps
  bodyFullShared gasShadowCompileStmtHelpers gasShadowCompile gasShadowState
  gasShadow externalEntryShape fragExec compileEnv vyperAST list

val ec_suffix = ``if bt = ECAdd then compile_ecadd_points x y
                  else compile_ecmul_point x y``;

Theorem ec_arith_compiler_cut[local]:
  (bt = ECAdd \/ bt = ECMul) /\
  expr_type e2 = (if bt = ECAdd then a else BaseT (UintT 256)) /\
  compile_expr cenv ty (Builtin a bt [e1;e2]) sa = (vv,sb) ==>
  ?x y s1 s2 res.
    lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr cenv (expr_type e2) e2 s1 = (y,s2) /\
    (^ec_suffix) s2 = (res,sb) /\ vv = FST (as_stack_val a (res,sb))
Proof
  disch_then (CONJUNCTS_THEN2 strip_assume_tac strip_assume_tac) >>
  gvs[] >> metis_tac[compile_ec_operands]
QED

Theorem ec_arith_shadow_children[local]:
  gas_shadow_state sa sha /\
  lower_value compile_expr cenv ty e sa = (x,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr e) sha = (y,shb) ==>
  y = x /\ gas_shadow_state sb shb
Proof
  strip_tac >> irule gas_shadow_step >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` (irule_at Any) >>
  qpat_assum `lower_value _ cenv _ e _ = _` (irule_at Any) >>
  simp[gas_shadow_stmt_lower_value_env]
QED

Theorem ec_arith_code_split[local]:
  cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\
  fn_has_code sa sb func ==>
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func
Proof
  strip_tac >>
  `cs_extends s1 sb` by (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  drule_all_then strip_assume_tac fn_has_code_split >> simp[] >>
  irule fn_has_code_split >> simp[]
QED

Theorem ec_arith_suffix_extends[local]:
  (^ec_suffix) s2 = (res,sb) ==> cs_extends s2 sb
Proof
  Cases_on `bt = ECAdd` >> simp[] >> strip_tac
  >- (qspecl_then [`x`,`y`,`s2`] mp_tac compile_ecadd_points_labels >> simp[]) >>
  qspecl_then [`x`,`y`,`s2`] mp_tac compile_ecmul_point_labels >> simp[]
QED

Theorem ec_arith_operand_code_mods:
  (bt = ECAdd \/ bt = ECMul) /\
  a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\ expr_type e1 = a /\
  expr_type e2 = (if bt = ECAdd then a else BaseT (UintT 256)) /\
  compile_expr cenv ty (Builtin a bt [e1;e2]) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Builtin a bt [e1;e2]))
    shadow_sa = (vv,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) ==>
  ?x y s1 s2 shadow_s1 shadow_s2 res shadow_res.
    lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr cenv (expr_type e2) e2 s1 = (y,s2) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
      (gas_shadow_expr e1) shadow_sa = (x,shadow_s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2)
      (gas_shadow_expr e2) shadow_s1 = (y,shadow_s2) /\
    (^ec_suffix) s2 = (res,sb) /\ (^ec_suffix) shadow_s2 = (shadow_res,shadow_sb) /\
    vv = FST (as_stack_val a (res,sb)) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,s1,shadow_sa,shadow_s1) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s1,s2,shadow_s1,shadow_s2) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s2,sb,shadow_s2,shadow_sb) /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= s2.cs_next_id
Proof
  PURE_REWRITE_TAC[expr_sim_full_code_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`x`,`y`,`s1`,`s2`,`res`] strip_assume_tac)
    ec_arith_compiler_cut >>
  `gas_shadow_expr (Builtin a bt [e1;e2]) =
    Builtin a bt [gas_shadow_expr e1;gas_shadow_expr e2]` by
    (qpat_assum `bt = ECAdd \/ bt = ECMul` strip_assume_tac >>
     simp[gas_shadow_expr_def, gas_shadow_builtin_def]) >>
  pop_assum (fn eq => qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (assume_tac o ONCE_REWRITE_RULE [eq])) >>
  `expr_type (gas_shadow_expr e2) = (if bt = ECAdd then a else BaseT (UintT 256))` by simp[] >>
  qpat_assum `compile_expr _ _ (Builtin _ _ [gas_shadow_expr _;gas_shadow_expr _]) _ = _`
    (mp_then (Pat `compile_expr _ _ _ _ = _`) mp_tac ec_arith_compiler_cut) >>
  (impl_tac >- simp[]) >>
  pure_rewrite_tac[gas_shadow_expr_type] >>
  disch_then (qx_choosel_then [`sx`,`sy`,`shadow_s1`,`shadow_s2`,`shadow_res`] strip_assume_tac) >>
  drule_all_then strip_assume_tac ec_arith_shadow_children >>
  qpat_x_assum `sx = x` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac ec_arith_shadow_children >>
  qpat_x_assum `sy = y` SUBST_ALL_TAC >>
  imp_res_tac (cj 2 compile_expr_grows) >>
  imp_res_tac ec_arith_suffix_extends >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    (irule ec_arith_code_split >> simp[]) >>
  `fn_has_code shadow_sa shadow_s1 shadow_func /\
   fn_has_code shadow_s1 shadow_s2 shadow_func /\
   fn_has_code shadow_s2 shadow_sb shadow_func` by
    (irule ec_arith_code_split >> simp[]) >>
  qpat_x_assum `vv = FST (as_stack_val _ (shadow_res,shadow_sb))` kall_tac >>
  qexistsl_tac [`x`,`y`,`s1`,`s2`,`shadow_s1`,`shadow_s2`,`res`,`shadow_res`] >>
  simp[]
QED
