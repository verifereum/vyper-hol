(* Linked equality and inequality on addresses and fixed bytes. *)
Theory bodyBopAddressBytesEqMods
Ancestors
  bodyBopWordOperandsMods bodyBopWordNormalPostMods bodyFullBopWordSuccess
  bodyFullBopBytesEqLayout bodyFullBopBytesEqSuffix bodyPtrBopScalarDispatch
  bodySimStmtFacts exprBodyPreProps exprSafeOperand exprWordOperand exprSimSource
  exprBopSimProps exprBopSimDefs exprSimCompare exprSimHyps
  vyperTypeSystem vyperTypeBuiltins vyperTypeEvalCaseProofs vyperTypeInvariants
  vyperTypeCallStackSoundness vyperValueOperation vyperValue vyperState
  vyperTyping vyperContext list exprSimHypsDefs vyperTypeCallGraph
  supportedExprTraverse allocLimits vyperStorageFootprint vyperInterpreter
  exprSimFullBundleProps bodyFullPostsMods bodyFullPredsMods gasShadowState
  vyperTypeExprSoundness vyperStorageTrace exprSimOperators
  gasOutcomeFullPostMods gasStorage freshWrites fragGasFresh fragExec
  loweringPosts exprLoweringProps exprSimMemDefs bodyPtrDefs compileEnv
  ptrDiscipline bodyFullShadowBodyInv valueEncoding
Libs monadsyntax

Theorem fixed_eq_typed_result[local]:
  (bop = Eq \/ bop = NotEq) /\
  (ty = BaseT AddressT \/ ?m. ty = BaseT (BytesT (Fixed m))) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v1 /\ value_has_type tv v2 ==>
  bop_result cx (BaseT BoolT) bop [ty;ty] v1 v2 es =
    INL (BoolV (eval_compare bop ty (typed_val_to_w256 tv v1)
                                    (typed_val_to_w256 tv v2)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?b1 b2. v1 = BytesV b1 /\ v2 = BytesV b2 /\
    (tv = BaseTV AddressT \/ ?m. tv = BaseTV (BytesT (Fixed m)) /\ m <= 32)` by
    (qpat_assum `ty = _ \/ _` strip_assume_tac >>
     gvs[evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
     Cases_on `v1` >> fs[value_has_type_def] >>
     Cases_on `v2` >> fs[value_has_type_def]) >>
  `typed_val_to_w256 tv v1 = typed_val_to_w256 tv v2 <=> v1 = v2` by
    (gvs[] >> irule typed_val_to_w256_bytes_11 >> simp[]) >>
  qpat_x_assum `bop = _ \/ _` strip_assume_tac >>
  qpat_x_assum `ty = _ \/ _` strip_assume_tac >>
  gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
      binop_negate_def, arithmeticPropsTheory.eval_compare_def, oEL_def,
      evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
  IF_CASES_TAC >> simp[]
QED

Theorem fixed_eq_static[local]:
  (bop = Eq \/ bop = NotEq) /\
  (expr_type e1 = BaseT AddressT \/ ?m. expr_type e1 = BaseT (BytesT (Fixed m))) /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  ann = BaseT BoolT /\ expr_type e2 = expr_type e1 /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  well_typed_expr env e1 /\ well_typed_expr env e2 /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >> simp[well_formed_type_def]) >>
  qpat_x_assum `well_typed_expr _ (Builtin _ _ _)`
    (strip_assume_tac o REWRITE_RULE [well_typed_expr_def, well_typed_builtin_app_def,
                                    constSubstCorrectTheory.frame_well_typed_exprs_cons]) >>
  `is_word_type (expr_type e1)` by
    (qpat_assum `well_typed_expr env e1` (drule_all_then mp_tac o
       MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] well_typed_expr_type_well_formed)) >>
     qpat_assum `expr_type e1 = _ \/ _` strip_assume_tac >>
     simp[well_formed_type_def, is_word_type_def, evaluate_type_def,
          optionTheory.IS_SOME_EXISTS, optionTheory.IF_EQUALS_OPTION]) >>
  `ann = BaseT BoolT /\ expr_type e2 = expr_type e1` by
    (qpat_assum `bop = _ \/ _` strip_assume_tac >>
     fs[well_typed_binop_def]) >>
  qpat_x_assum `env.type_defs = get_tenv cx` kall_tac >>
  qpat_x_assum `well_typed_binop _ _ _ _` mp_tac >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem fixed_eq_child_pres[local]:
  expr_body_pre_mods mods ce cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_body_pre_mods mods ce cx env e1 es /\
  (!mid. expr_sim_inv_mods mods ce cx env mid ==> expr_body_pre_mods mods ce cx env e2 mid)
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, well_typed_builtin_app_def,
       int_calls_expr_def, byte_widths_expr_def, alloc_limits_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, EVERY_APPEND] >>
  strip_tac >>
  drule_then assume_tac call_evaluation_safe_append_left >>
  drule_then assume_tac call_evaluation_safe_append_right >>
  fs[constSubstCorrectTheory.frame_well_typed_exprs_cons]
QED

Theorem fixed_eq_child_source[local]:
  expr_body_pre_mods mods ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) ==>
  expr_sim_inv_mods mods ce cx env ee /\
  (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!st0 H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace)
Proof
  strip_tac >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >> strip_tac >>
  drule_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  simp[] >> conj_tac >- fs[value_runtime_typed_def] >>
  conj_tac >- (drule (REWRITE_RULE [ETA_AX] bop_value_scopes_dom) >> simp[]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  rpt strip_tac >>
  qpat_assum `storage_trace_frame _` (drule_all_then mp_tac o MATCH_MP
    (REWRITE_RULE [GSYM AND_IMP_INTRO] valid_horizon_frame)) >> simp[]
QED

Theorem fixed_eq_operand[local]:
  expr_post_mods H ctx func ce cx e es sa sb s0 ee v op t /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  eval_operand op t = SOME (typed_val_to_w256 tv v)
Proof
  strip_tac >> fs[expr_post_mods_def,expr_post_def,post_value_type_word] >>
  drule_all expr_val_rel_typed >> simp[]
QED

Theorem fixed_eq_operand_frame[local]:
  expr_post_mods H ctx func ce cx e es sa sb s0 ee v op t /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ (!l. x <> Label l) /\
  eval_operand x s0 = SOME w ==>
  eval_operand x t = SOME w
Proof
  strip_tac >> irule eval_operand_frame >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`sa`,`s0`] >> fs[expr_post_mods_def,expr_post_def]
QED

Theorem fixed_eq_input_kept[local]:
  ghost_kept_at lo ce mid s1 G1 tn1 t G2 tn2 /\
  (!z. x = Var z ==> not_fresh_at s1 z) ==>
  op_prov G2 x = op_prov G1 x /\ op_taint tn2 x = op_taint tn1 x
Proof
  Cases_on `x` >> simp[op_prov_def, op_taint_def] >>
  simp[ghost_kept_at_def, op_taint_def]
QED

Theorem bop_address_bytes_eq_value_sim_mods:
  (bop = Eq \/ bop = NotEq) /\
  (expr_type e1 = BaseT AddressT \/ ?m. expr_type e1 = BaseT (BytesT (Fixed m))) /\
  body_exprs_full_ok_mods mods exps cx [e1;e2] /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac fixed_eq_static >>
  PURE_REWRITE_TAC[expr_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac bop_bytes_eq_layout >>
  qpat_assum `lower_value compile_expr cenv _ e1 sa = _`
    (qspec_then `env` mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] lower_value_word_shape)) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `lower_value compile_expr cenv _ e2 s1 = _`
    (qspec_then `env` mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] lower_value_word_shape)) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `cs_extends s2 sb /\ cs_extends sh2 shadow_sb` by metis_tac[compile_binop_shape] >>
  `cs_extends shadow_sa sh1 /\ cs_extends sh1 sh2` by metis_tac[cj 2 compile_expr_grows] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
   fn_has_code shadow_sa sh1 shadow_func /\ fn_has_code sh1 sh2 shadow_func` by
    (`cs_extends sa s2 /\ cs_extends s1 sb /\ cs_extends sh1 shadow_sb` by
       (rpt conj_tac >> irule cs_extends_trans >> first_assum (irule_at Any) >> simp[]) >>
     rpt conj_tac >> irule fn_has_code_mid >>
     first_assum (fn th => if can (match_term ``fn_has_code _ _ _``) (concl th)
                          then irule_at Any th else NO_TAC) >> simp[cs_extends_refl]) >>
  `bop <> In /\ bop <> NotIn` by (qpat_assum `bop = Eq \/ _` strip_assume_tac >> simp[]) >>
  qpat_x_assum `ann = BaseT BoolT` SUBST_ALL_TAC >>
  irule bop_operands_cps_exit_mods >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ _ _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ _ e1 sa = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ _ e2 s1 = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ _ (gas_shadow_expr e1) shadow_sa = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ _ (gas_shadow_expr e2) sh1 = _` (irule_at Any) >>
  qexistsl_tac [`shadow_func`,`exps`] >> simp[expr_sim_full_code_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> immutable_frame_mods func cenv cx es s0` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >> suspend "suffix"
QED

Resume bop_address_bytes_eq_value_sim_mods[suffix]:
  qx_genl_tac [`left`,`v1`,`mid`,`G1`,`tn1`,`t`,`right`,`v2`,`fin`,`G2`,`tn2`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac fixed_eq_child_pres >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace /\
   valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (qspec_then `storage_trace_horizon fin.storage_trace` (drule_then strip_assume_tac)) >>
  `mid with gas_obs := [] = mid /\ fin with gas_obs := [] = fin` by
    simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE bool_ss [APPEND_NIL])) >>
  qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE bool_ss [APPEND_NIL])) >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit left s0.vs_gas_readings) = (INL v1,mid)` by
    (qpat_assum `bind (eval_expr cx e1) _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  `bind (eval_expr cx e2) (read_result cx)
     (mid with gas_obs := gas_explicit right t.vs_gas_readings) = (INL v2,fin)` by
    (qpat_assum `bind (eval_expr cx e2) _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  drule_all_then strip_assume_tac fixed_eq_child_source >>
  qpat_assum `!mid. expr_sim_inv_mods _ _ _ _ mid ==> _`
    (qspec_then `mid` (drule_then assume_tac)) >>
  drule_all_then strip_assume_tac fixed_eq_child_source >>
  `tv' = tv` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tv' = tv` SUBST_ALL_TAC >>
  `eval_operand x t = SOME (typed_val_to_w256 tv v1) /\
   eval_operand y u = SOME (typed_val_to_w256 tv v2)` by
    (conj_tac >-
       (qpat_assum `expr_post_mods _ _ _ _ _ e1 _ _ _ _ _ _ _ t`
         (mp_then Any mp_tac fixed_eq_operand) >> simp[]) >>
     qpat_assum `expr_post_mods _ _ _ _ _ e2 _ _ _ _ _ _ _ u`
       (mp_then Any mp_tac fixed_eq_operand) >> simp[]) >>
  `eval_operand x u = SOME (typed_val_to_w256 tv v1)` by
    (qpat_assum `expr_post_mods _ _ _ _ _ e2 _ _ _ _ _ _ _ u`
       (mp_then Any mp_tac fixed_eq_operand_frame) >>
     disch_then irule >> asm_rewrite_tac[]) >>
  `!z. x = Var z ==> not_fresh_at s2 z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `s1` >> simp[]) >>
  drule_all bop_bytes_eq_suffix_run >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts s2 sb) u = OK r` >>
  `bop_result cx (BaseT BoolT) bop [expr_type e1;expr_type e1] v1 v2 fin =
   INL (BoolV (eval_compare bop (expr_type e1) (typed_val_to_w256 tv v1)
                 (typed_val_to_w256 tv v2)))` by (irule fixed_eq_typed_result >> simp[]) >>
  `?B. bop_scalar_seq {z | not_fresh_at s2 z} ({x;y} UNION IMAGE Lit UNIV)
         (emitted_insts s2 sb) B /\ op IN B` by
    (irule bop_scalar_binop_certificate >> simp[] >>
     qpat_assum `compile_binop _ _ _ _ _ _ s2 = _` (irule_at Any) >>
     qpat_assum `well_typed_binop _ _ _ _` (irule_at Any) >> simp[]) >>
  suspend "path"
QED

Resume bop_address_bytes_eq_value_sim_mods[path]:
  `op_prov G2 x = NONE /\ op_taint tn2 x = {} /\
   op_prov G2 y = NONE /\ op_taint tn2 y = {}` by
    (`op_prov G2 x = op_prov G1 x /\ op_taint tn2 x = op_taint tn1 x` by
       (irule fixed_eq_input_kept >>
        qpat_assum `ghost_kept_at _ _ mid s1 _ _ t _ _` (irule_at Any) >> simp[]) >>
     fs[post_value_type_word, ptr_val_ok_def]) >>
  `!a. a IN ({x;y} UNION IMAGE Lit UNIV) ==>
       op_prov G2 a = NONE /\ op_taint tn2 a = {}` by
    (mp_tac (Q.INST [`x` |-> `x`, `y` |-> `y`, `G` |-> `G2`, `tn` |-> `tn2`]
       bop_scalar_binop_input_clean) >> simp[]) >>
  `allocas_from lo u` by fs[ghost_inv_at_mods_def] >>
  `straight_fresh (compile_binop bop x y (expr_type e1) NONE NONE)` by
    (irule straight_fresh_compare >> qpat_assum `bop = Eq \/ _` strip_assume_tac >> simp[]) >>
  drule_all_then strip_assume_tac straight_fresh_code_prefix >>
  drule_all bop_word_scalar_success_joint >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `eval_operand op r = SOME (bool_to_word b)` >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G'`,`fin`,`INL (BoolV b)`,
    `r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb)`,`tn'`] >>
  simp[] >> gen_tac >> strip_tac >> suspend "post"
QED

Resume bop_address_bytes_eq_value_sim_mods[post]:
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `!st0 H. valid_horizon _ _ H fin.storage_trace ==> _`
       (drule_then ACCEPT_TAC)) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!st0 H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then ACCEPT_TAC)) >>
  qpat_assum `!h. valid_horizon _ _ h es.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!h. valid_horizon _ _ h fin.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `expr_val_rel cx (BaseT BoolT) (BoolV b) op r` by
    (simp[expr_val_rel_def, is_word_type_def, evaluate_type_def,
          typed_val_to_w256_def, val_to_w256_def] >>
     Cases_on `b` >> simp[venomExecSemanticsTheory.bool_to_word_def]) >>
  `bop <> Exp` by (qpat_assum `bop = Eq \/ _` strip_assume_tac >> simp[]) >>
  qpat_assum `!a. a IN B ==> _` (qspec_then `op` (drule_then strip_assume_tac)) >>
  `!z. not_fresh_at s2 z ==> FLOOKUP G' z = FLOOKUP G2 z /\
       FLOOKUP tn'.t_var z = FLOOKUP tn2.t_var z` by
    (qpat_assum `!z. z IN {z | not_fresh_at s2 z} ==> _` mp_tac >> simp[]) >>
  mp_tac (Q.INST_TYPE [`:'a` |-> `:256`]
    (Q.INST [`ann` |-> `BaseT BoolT`,`v` |-> `BoolV b`]
      (SRULE [LET_THM] bop_word_normal_post_mods))) >>
  (impl_tac >- simp[is_word_type_def]) >>
  simp[vyperASTTheory.expr_type_def, post_value_type_word, is_word_type_def] >>
  strip_tac >> simp[expr_store_bound_word, ptr_val_ok_word, is_word_type_def]
QED

Finalise bop_address_bytes_eq_value_sim_mods
