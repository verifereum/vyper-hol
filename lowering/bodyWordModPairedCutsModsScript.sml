(* Paired real/shadow compiler cuts for linked modular builtins. *)
Theory bodyWordModPairedCutsMods
Ancestors bodySimFull[qualified,ignore_grammar] exprSimHypsDefs[qualified,ignore_grammar] builtinMath[qualified,ignore_grammar] gasShadowUnit[qualified,ignore_grammar] venomWf[qualified,ignore_grammar] freshWrites[qualified,ignore_grammar]
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv
  exprBodyPreProps exprSimWordBuiltins exprLoweringProps exprWordOperand exprSimSource
  exprSimFullBundleProps exprSimUnopProps
  gasShadowCompileStmtHelpers gasShadowState gasShadow fragExec
  exprLowering loweringPosts compileEnv vyperTypeSystem vyperContext
  vyperAST vyperInterpreter vyperTypeInvariants list finite_map

Theorem modular_code_cuts[local]:
  cs_extends a b /\ cs_extends b c /\ cs_extends c d /\ cs_extends d e /\
  fn_has_code a e fn ==>
  fn_has_code a b fn /\ fn_has_code b c fn /\
  fn_has_code c d fn /\ fn_has_code d e fn
Proof
  strip_tac >>
  `cs_extends c e` by (irule cs_extends_trans >> qexists_tac `d` >> simp[]) >>
  `cs_extends b e` by (irule cs_extends_trans >> qexists_tac `c` >> simp[]) >>
  `fn_has_code a b fn /\ fn_has_code b e fn` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code b c fn /\ fn_has_code c e fn` by
    (irule fn_has_code_split >> simp[]) >>
  simp[] >> irule fn_has_code_split >> simp[]
QED

Theorem modular_word_operand_shape[local]:
  !mods cx env es cenv ty e a x b.
    lower_value compile_expr cenv ty e a = (x,b) ==>
    expr_body_pre_mods mods cenv cx env e es /\ is_word_type (expr_type e) ==>
    (!q. x = Var q ==> not_fresh_at b q) /\ (!l. x <> Label l)
Proof
  rpt gen_tac >> disch_tac >> strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def,env_context_consistent_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     drule_all_then ACCEPT_TAC env_consistent_var_type_evaluates) >>
  drule_all_then strip_assume_tac lower_value_word_shape >> simp[]
QED

Theorem modular_shadow_operand[local]:
  lower_value compile_expr cenv ty e a = (x,b) /\ gas_shadow_state a sha ==>
  ?shb. lower_value compile_expr (gas_shadow_env T cenv) ty
          (gas_shadow_expr e) sha = (x,shb) /\ gas_shadow_state b shb
Proof
  strip_tac >>
  `gas_shadow_compiles (lower_value compile_expr cenv ty e)
     (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
    simp[gas_shadow_stmt_lower_value_env] >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha` >>
  qpat_x_assum `gas_shadow_compiles _ _` mp_tac >> simp[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`a`,`sha`] mp_tac) >> simp[]
QED

Theorem modular_suffix_grows[local]:
  !bt x y z a op b.
    (if bt = vyperAST$AddMod then compile_addmod else compile_mulmod) x y z a = (op,b) ==>
    cs_extends a b
Proof
  rpt gen_tac >> strip_tac >>
  `straight_fresh ((if bt = AddMod then compile_addmod else compile_mulmod) x y z)` by
    (Cases_on `bt = AddMod` >> simp[straight_fresh_compile_modular]) >>
  drule_all_then strip_assume_tac straight_fresh_cs_extends >> simp[]
QED

Theorem modular_paired_cuts_mods:
  (bt = AddMod \/ bt = MulMod) /\
  expr_type e1 = BaseT (UintT 256) /\
  expr_type e2 = BaseT (UintT 256) /\
  expr_type e3 = BaseT (UintT 256) /\
  expr_body_pre_mods mods cenv cx env e1 es /\
  expr_body_pre_mods mods cenv cx env e2 es /\
  expr_body_pre_mods mods cenv cx env e3 es /\
  lower_value compile_expr cenv ty (Builtin ann bt [e1;e2;e3]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann bt [e1;e2;e3])) shadow_sa = (op,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func)
    (sa,sb,shadow_sa,shadow_sb) ==>
  ?x s1 sh1 y s2 sh2 z s3 sh3.
    lower_value compile_expr cenv ty e1 sa = (x,s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1)
      shadow_sa = (x,sh1) /\ gas_shadow_state s1 sh1 /\
    lower_value compile_expr cenv ty e2 s1 = (y,s2) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e2)
      sh1 = (y,sh2) /\ gas_shadow_state s2 sh2 /\
    lower_value compile_expr cenv ty e3 s2 = (z,s3) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e3)
      sh2 = (z,sh3) /\ gas_shadow_state s3 sh3 /\
    (if bt = AddMod then compile_addmod else compile_mulmod) x y z s3 =
      (op,sb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,s1,shadow_sa,sh1) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s1,s2,sh1,sh2) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s2,s3,sh2,sh3) /\
    fn_has_code s3 sb func /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
    sa.cs_next_var <= s1.cs_next_var /\
    s1.cs_next_var <= s2.cs_next_var /\
    s2.cs_next_var <= s3.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\
    s1.cs_next_id <= s2.cs_next_id /\
    s2.cs_next_id <= s3.cs_next_id /\
    (!q. x = Var q ==> not_fresh_at s1 q) /\
    (!q. y = Var q ==> not_fresh_at s2 q) /\
    (!q. z = Var q ==> not_fresh_at s3 q) /\
    (!l. x <> Label l) /\ (!l. y <> Label l) /\ (!l. z <> Label l)
Proof
  disch_then (EVERY o map ASSUME_TAC o CONJUNCTS) >>
  drule_then strip_assume_tac expr_sim_full_code_fields >>
  qpat_assum `lower_value _ _ _ (Builtin _ _ _) _ = _`
    (mp_then Any mp_tac lower_value_ternary_modular) >> simp[] >>
  disch_then (qx_choose_then `x` (qx_choose_then `s1`
    (qx_choose_then `y` (qx_choose_then `s2`
      (qx_choose_then `z` (qx_choose_then `s3` strip_assume_tac)))))) >>
  `?sh1. lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr e1) shadow_sa = (x,sh1) /\ gas_shadow_state s1 sh1` by
    (irule modular_shadow_operand >> qexists_tac `sa` >> simp[]) >>
  `?sh2. lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr e2) sh1 = (y,sh2) /\ gas_shadow_state s2 sh2` by
    (irule modular_shadow_operand >> qexists_tac `s1` >> simp[]) >>
  `?sh3. lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr e3) sh2 = (z,sh3) /\ gas_shadow_state s3 sh3` by
    (irule modular_shadow_operand >> qexists_tac `s2` >> simp[]) >>
  `cs_extends s3 sb` by (drule modular_suffix_grows >> simp[]) >>
  `cs_extends sh3 shadow_sb` by
    (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _` mp_tac >>
     `gas_shadow_builtin bt = bt` by
       (qpat_assum `bt = AddMod \/ bt = MulMod` strip_assume_tac >>
        simp[gas_shadow_builtin_def]) >>
     simp[gas_shadow_expr_def,MAP] >>
     disch_then (mp_then Any mp_tac lower_value_ternary_modular) >>
     simp[] >>
     disch_then (mp_tac o MATCH_MP modular_suffix_grows) >> simp[]) >>
  imp_res_tac (cj 2 compile_expr_grows) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    (irule modular_code_cuts >> simp[]) >>
  `fn_has_code shadow_sa sh1 shadow_func /\ fn_has_code sh1 sh2 shadow_func /\
   fn_has_code sh2 sh3 shadow_func /\ fn_has_code sh3 shadow_sb shadow_func` by
    (irule modular_code_cuts >> simp[]) >>
  `(!q. x = Var q ==> not_fresh_at s1 q) /\ (!l. x <> Label l)` by
    (qpat_assum `lower_value compile_expr cenv ty e1 sa = _`
       (mp_then Any mp_tac modular_word_operand_shape) >>
     disch_then (qspecl_then [`mods`,`cx`,`env`,`es`] mp_tac) >> simp[is_word_type_def]) >>
  `(!q. y = Var q ==> not_fresh_at s2 q) /\ (!l. y <> Label l)` by
    (qpat_assum `lower_value compile_expr cenv ty e2 s1 = _`
       (mp_then Any mp_tac modular_word_operand_shape) >>
     disch_then (qspecl_then [`mods`,`cx`,`env`,`es`] mp_tac) >> simp[is_word_type_def]) >>
  `(!q. z = Var q ==> not_fresh_at s3 q) /\ (!l. z <> Label l)` by
    (qpat_assum `lower_value compile_expr cenv ty e3 s2 = _`
       (mp_then Any mp_tac modular_word_operand_shape) >>
     disch_then (qspecl_then [`mods`,`cx`,`env`,`es`] mp_tac) >> simp[is_word_type_def]) >>
  qexistsl_tac [`x`,`s1`,`sh1`,`y`,`s2`,`sh2`,`z`,`s3`,`sh3`] >>
  simp[expr_sim_full_code_def]
QED
