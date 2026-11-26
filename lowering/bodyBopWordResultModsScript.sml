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
  exprLoweringProps compileEnv bodyBopWordReachedRunMods bodyBopWordNormalPostMods
  vyperStorageTrace vyperStorageFootprint exprSimProps bodyFullPostsMods
  bodyFullShadowBodyInv list bodyPtrDefs ptrDiscipline exprSimDefs vyperAST
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

Theorem bop_word_read_horizon[local]:
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs) =
    (INL v, ee with gas_obs := ys) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >> drule_at (Pat `_ = _`) valid_horizon_frame >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >> disch_then irule >> simp[]
QED

Theorem bop_word_value_sim_mods:
  bop <> In /\ bop <> NotIn /\
  word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
  body_exprs_full_ok_mods mods exps cx [e1;e2] /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin ann (Bop bop) [e1;e2]) es
Proof
  strip_tac >> drule_then strip_assume_tac bop_word_parent_static >>
  imp_res_tac word_value_type_word >>
  rw[expr_sim_full_mods_def] >>
  mp_tac (SPEC_ALL bop_word_paired_layout_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,s1,shadow_sa,shadow_s1) /\
   expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s1,s2,shadow_s1,shadow_s2)` by
    simp[expr_sim_full_code_def] >>
  irule bop_operands_cps_exit_mods >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qexistsl_tac [`d`,`s1`,`s2`,`sa`,`shadow_func`,`shadow_s1`,
        `shadow_s2`,`shadow_sa`,`x`,`y`] >> simp[] >>
      conj_tac >- suspend "reached" >>
      gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]
QED

Resume bop_word_value_sim_mods[reached]:
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`ce` |-> `cenv`] (SPEC_ALL bop_word_reached_run_mods)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
    gen_tac >> strip_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[])) >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac
    (CONJUNCTS_THEN2 strip_assume_tac
      (CONJUNCTS_THEN2 strip_assume_tac (CONJUNCTS_THEN2 strip_assume_tac assume_tac)))) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace /\
   valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
     fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (qspec_then `storage_trace_horizon fin.storage_trace` (drule_then strip_assume_tac)) >>
  `op_prov G2 x = NONE /\ op_taint tn2 x = {} /\
   op_prov G2 y = NONE /\ op_taint tn2 y = {}` by
    (`op_prov G2 x = op_prov G1 x /\ op_taint tn2 x = op_taint tn1 x` by
       (Cases_on `x` >> gvs[op_prov_def, op_taint_def, ghost_kept_at_def]) >>
     fs[post_value_type_word, ptr_val_ok_def]) >>
  `!a. a IN ({x;y} UNION IMAGE Lit UNIV) ==>
       op_prov G2 a = NONE /\ op_taint tn2 a = {}` by
    (mp_tac (Q.INST [`x` |-> `x`, `y` |-> `y`, `G` |-> `G2`, `tn` |-> `tn2`]
       bop_scalar_binop_input_clean) >> simp[]) >>
  `allocas_from lo u` by fs[ghost_inv_at_mods_def] >>
  `sb.cs_current_bb = s2.cs_current_bb /\
   sb.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 sb` by
    (`MEM bop [Add;Sub;Mul;Div;Mod;UnsafeAdd;UnsafeSub;UnsafeMul;UnsafeDiv;
        And;Or;XOr;ShL;ShR;Eq;NotEq;Lt;LtE;Gt;GtE;Exp;Min;Max;In;NotIn]` by
       (qpat_assum `well_typed_binop _ _ _ _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> Cases_on `bop` >> simp[well_typed_binop_def]) >>
     drule augAssignPtrCompilerTheory.compile_binop_straight_fresh_ptr >>
     simp[straight_fresh_def] >> disch_then drule >> simp[]) >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts s2 sb) (DROP u.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code s2 sb func`
       (mp_tac o REWRITE_RULE [fn_has_code_def]) >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >>
     strip_tac >> qexists_tac `bb` >> simp[DROP_APPEND]) >>
  qpat_x_assum `(?v r. _) \/ _` strip_assume_tac
  >- suspend "success" >> suspend "abort"
QED

Resume bop_word_value_sim_mods[success]:
  drule_all bop_word_scalar_success_joint >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G'`,`fin`,`INL v`,
    `r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb)`,`tn'`] >>
  simp[] >> gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (irule bop_word_read_horizon >>
     qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
       (qspec_then `[]` (irule_at Any)) >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (irule bop_word_read_horizon >>
     qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
       (qspec_then `[]` (irule_at Any)) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!h. valid_horizon _ _ h es.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. valid_horizon _ _ h fin.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `expr_val_rel cx ann v op r` by
    simp[expr_val_rel_def, typed_val_to_w256_word_value] >>
  qpat_assum `!a. a IN B ==> _` (qspec_then `op` (drule_then strip_assume_tac)) >>
  `!z. not_fresh_at s2 z ==> FLOOKUP G' z = FLOOKUP G2 z /\
       FLOOKUP tn'.t_var z = FLOOKUP tn2.t_var z` by
    (qpat_assum `!z. z IN {z | not_fresh_at s2 z} ==> _` mp_tac >> simp[]) >>
  mp_tac (Q.INST_TYPE [`:'a` |-> `:256`]
    (SRULE [LET_THM] bop_word_normal_post_mods)) >>
  (impl_tac >- simp[]) >>
  simp[expr_type_def, post_value_type_word]
QED

Resume bop_word_value_sim_mods[abort]:
  drule_all bop_word_scalar_abort_joint >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  irule gas_outcome_full_mods_exit_revert >> simp[] >>
  qexistsl_tac [`G'`,`fin`,`INR (Error (RuntimeError m))`,`tn'`,
    `r with vs_inst_idx := j`] >>
  simp[expr_exit_def, halt_exit_def, exit_result_def]
QED

Finalise bop_word_value_sim_mods
