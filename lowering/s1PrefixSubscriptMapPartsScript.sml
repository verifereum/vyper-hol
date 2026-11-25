Theory s1PrefixSubscriptMapParts
Ancestors
  exprSimMapKey exprLoweringProps fragExec gasShadowCompileStmtHelpers
  gasShadowCompileBase gasShadowCompilePure gasShadowState gasShadow
  exprLowering compileEnv vyperAST

Theorem mapping_subscript_code_parts[local]:
  compile_expr cenv ty (Subscript ann e1 e2) sa = (vv,sb) /\
  place_type cenv e1 = MapPT kt vt /\
  ~copies_subscript_base cenv e1 e2 /\ fn_has_code sa sb func ==>
  ?bvv sm key sn.
    compile_expr cenv ty e1 sa = (bvv,sm) /\
    lower_value compile_expr cenv (expr_type e2) e2 sm = (key,sn) /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\
    cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id
Proof
  strip_tac >> drule_all compile_expr_mapping_subscript_parts >> strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by (drule (cj 1 compile_expr_grows) >> simp[]) >>
  `cs_extends sm sn` by (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `cs_extends sn sp` by
    (Cases_on `is_bytestring_type kt` >> gvs[cs_extends_refl] >>
     qspecl_then [`key`, `F`, `sn`] mp_tac ci_mono_compile_keccak256_key >>
     simp[ci_mono_def]) >>
  `cs_extends sp sb` by
    (qspecl_then [`vv_operand bvv`, `hashed`, `sp`] mp_tac
       ci_mono_compile_mapping_subscript >> simp[ci_mono_def]) >>
  `cs_extends sn sb /\ cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `fn_has_code sm sn func` by (drule_all fn_has_code_split >> simp[]) >>
  qexistsl_tac [`bvv`, `sm`, `key`, `sn`] >> simp[]
QED

Theorem mapping_subscript_prefix_parts:
  place_type cenv e1 = MapPT kt vt /\ ~copies_subscript_base cenv e1 e2 /\
  compile_expr cenv ty (Subscript ann e1 e2) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Subscript ann e1 e2)) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?bvv sm shadow_sm key sn shadow_sn.
    compile_expr cenv ty e1 sa = (bvv,sm) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1) shadow_sa =
      (bvv,shadow_sm) /\
    lower_value compile_expr cenv (expr_type e2) e2 sm = (key,sn) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2)
      (gas_shadow_expr e2) shadow_sm = (key,shadow_sn) /\
    gas_shadow_state sm shadow_sm /\ gas_shadow_state sn shadow_sn /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\
    fn_has_code shadow_sm shadow_sn shadow_func /\
    cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id
Proof
  strip_tac >> drule_all mapping_subscript_code_parts >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (assume_tac o REWRITE_RULE [gas_shadow_expr_def]) >>
  `place_type (gas_shadow_env T cenv) (gas_shadow_expr e1) = MapPT kt vt` by simp[] >>
  `~copies_subscript_base (gas_shadow_env T cenv) (gas_shadow_expr e1)
      (gas_shadow_expr e2)` by
    fs[copies_subscript_base_gas_shadow_env,copies_subscript_base_def,
       gas_shadow_subscript_overlap] >>
  qpat_assum `compile_expr _ _ (Subscript _ (gas_shadow_expr _) _) _ = _`
    (mp_then (Pos hd) mp_tac mapping_subscript_code_parts) >>
  simp[] >> disch_then (qspec_then `shadow_func` mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `fn_has_code shadow_sa mshadow shadow_func` >>
  rename1 `fn_has_code mshadow nshadow shadow_func` >>
  `gas_shadow_compiles (compile_expr cenv ty e1)
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1))` by
    irule gas_shadow_stmt_compile_expr_env >>
  pop_assum (qspecl_then [`sa`, `shadow_sa`] mp_tac o
    REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e2) e2)
     (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2)
       (gas_shadow_expr e2))` by irule gas_shadow_stmt_lower_value_env >>
  pop_assum (qspecl_then [`sm`, `mshadow`] mp_tac o
    REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  metis_tac[]
QED
