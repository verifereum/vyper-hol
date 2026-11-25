(* The checked scalar suffix after both forced linked Bop operands. *)
Theory bodyBopWordResultMods
Ancestors
  bodyBopWordOperandsMods bodyFullBopWordLayout bodyFullBopWordExtract
  bodyFullBopWordPost bodyFullBopWordSuccess bodyFullBopWordAbort
  bodyForRangeScalarFrameMods bodySimStmtFacts exprBodyPreProps
  exprWordOperand exprSafeOperand exprBopLowering exprSimOperators
  gasShadowCompileStmtHelpers exprSimFullBundleProps gasOutcomeFullPostMods
  exprSimSource exprBopSimProps bodyPtrBopSource bodyPtrBopScalarRun
  bodyPtrBopScalarDispatch bodyPtrBopScalarOutcome bodyBinopFragMemory
  gasStorage freshWrites fragExec loweringPosts exprSimMemDefs
  vyperTypeInvariants vyperTypeSystem vyperTypeBuiltins vyperState
  vyperTypeEvalCaseProofs exprSimHyps valueCopyBytes gasShadow gasShadowState
  exprLoweringProps compileEnv
Libs monadsyntax

Theorem bop_word_parent_static[local]:
  expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  well_typed_expr env e1 /\ well_typed_expr env e2 /\
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  (bop = Exp ==> IS_SOME (expr_int_literal e1) \/
    ?n. expr_int_literal e2 = SOME n /\ 0 <= n) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e2) /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  env.type_defs = get_tenv cx
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
     simp[well_formed_type_def]) >>
  qpat_x_assum `well_typed_expr _ (Builtin _ _ _)`
    (mp_tac o REWRITE_RULE [well_typed_expr_def, well_typed_builtin_app_def]) >>
  simp[constSubstCorrectTheory.frame_well_typed_exprs_cons] >> strip_tac >>
  conj_tac
  >- (disch_tac >> gvs[builtin_operands_ok_def, expr_int_literal_value] >>
      drule power_operands_ok_literal >> simp[nonneg_int_literal_def] >>
      Cases_on `int_literal_value e2` >> simp[]) >>
  reverse conj_tac >- metis_tac[] >>
  disch_then strip_assume_tac >> gvs[builtin_operands_ok_def]
QED

Theorem bop_word_paired_layout_mods[local]:
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  bop <> In /\ bop <> NotIn /\
  well_typed_expr env e1 /\ well_typed_expr env e2 /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann (Bop bop) [e1;e2])) shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?x y s1 s2 shadow_s1 shadow_s2.
    lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
      (gas_shadow_expr e1) shadow_sa = (x,shadow_s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
      (gas_shadow_expr e2) shadow_s1 = (y,shadow_s2) /\
    compile_binop bop x y (expr_type e1)
      (if bop = Exp then expr_int_literal e1 else NONE)
      (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
    gas_shadow_state s1 shadow_s1 /\ gas_shadow_state s2 shadow_s2 /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\
    (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
    (!z. y = Var z ==> not_fresh_at s2 z) /\ (!l. y <> Label l) /\
    fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
    fn_has_code shadow_sa shadow_s1 shadow_func /\
    fn_has_code shadow_s1 shadow_s2 shadow_func
Proof
  strip_tac >>
  `~is_bytestring_type (expr_type e1)` by metis_tac[is_bytestring_word_type] >>
  drule lower_value_bop >> simp[] >> strip_tac >>
  qpat_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[NoAsms, gas_shadow_expr_def, gas_shadow_builtin_def] >> strip_tac >>
  drule lower_value_bop >> simp[gas_shadow_expr_type] >> strip_tac >>
  `x' = x /\ gas_shadow_state s1 s1'` by
    (mp_tac (Q.INST [`sd` |-> `T`, `ty` |-> `expr_type e1`, `e` |-> `e1`]
       gas_shadow_stmt_lower_value_env) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  `y' = y /\ gas_shadow_state s2 s2'` by
    (mp_tac (Q.INST [`sd` |-> `T`, `ty` |-> `expr_type e1`, `e` |-> `e2`]
       gas_shadow_stmt_lower_value_env) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s1`, `s1'`] mp_tac) >> simp[]) >>
  gvs[] >>
  qpat_assum `lower_value compile_expr cenv _ e1 sa = _`
    (qspec_then `env` mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] lower_value_word_shape)) >>
  simp[] >> strip_tac >>
  qpat_assum `lower_value compile_expr cenv _ e2 s1 = _`
    (qspec_then `env` mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] lower_value_word_shape)) >>
  simp[] >> strip_tac >>
  `cs_extends s2 sb /\ cs_extends s2' shadow_sb` by metis_tac[compile_binop_shape] >>
  `cs_extends shadow_sa s1' /\ cs_extends s1' s2'` by
    metis_tac[cj 2 compile_expr_grows] >>
  simp[] >>
  metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl]
QED
