(* Seam 2 joint induction, For family: a Range whose endpoints are not both
   integer literals, compiled with the checked range prefix. *)
Theory bodyIntCallFamStmtForChecked
Ancestors
  bodyIntCallFamStmtForRange bodyIntCallFamStmtForCheckedTail
  bodyIntCallFamStmtForCheckedStatic bodyIntCallFamStmtForCheckedCompiled
  bodyIntCallFamStmtForCheckedEndpoint bodyIntCallFamStmtForTyping
  bodyIntCallJointContract bodySim loweringPosts compileEnv stmtSimForRange
  bodyIntCallJointStmtSeq stmtSimProps stmtSimDefs stmtLowering compileVyper stmtSimForParts
  vyperTypeSystem vyperTyping supportedStmts supportedStmtTraverse supportedExprs
  exprSimHypsDefs vyperTypeInvariants exprSimSource
  vyperInterpreter vyperState list vyperTypeCallGraph finite_map

Theorem intcall_stmts_producer_for_range_checked:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  intcall_stmts_producer fp stmts /\
  ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) ==>
  intcall_stmts_producer fp [For id fty (Range e1 e2) bound stmts]
Proof
  strip_tac >> simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  `type_stmt env fp.jc_ret_ty (For id fty (Range e1 e2) bound stmts) = SOME env'` by
    fs[type_stmt_def, AllCaseEqs()] >>
  drule (SIMP_RULE std_ss [pairTheory.FORALL_PROD]
    (CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX)))
      bodySimDeclCasesTheory.body_range_typing)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  gvs[supported_stmt_def, supported_checked_range_contract,
      int_calls_stmt_def, supported_stmt_expr_exists_def] >>
  rename1 `is_int_type fty` >>
  `FLOOKUP ce.ce_vars id = NONE` by
    (fs[intcall_joint_res_def, intcall_expr_res_def, ce_locals_declared_def] >>
     Cases_on `FLOOKUP ce.ce_vars id` >> metis_tac[]) >>
  `env.type_defs = get_tenv fp.jc_cx` by
    fs[intcall_joint_res_def, intcall_expr_res_def, expr_sim_inv_def,
       env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv fp.jc_cx) fty = SOME tyv` by
    fs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  `ce.ce_alloca_locals` by fs[body_inv_def] >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton, stmt_env_def, declare_stmt_local_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> fs[] >>
  `!c lc sa sb. compile_stmts c lc
      (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty) stmts sa = ((),sb) ==>
      cs_extends sa sb` by
    metis_tac[stmtLoweringMonoTheory.compile_stmt_cs_mono, fragExecTheory.cs_mono_def] >>
  Cases_on `lower_value compile_expr ce fty e1 sa` >>
  rename1 `_ = (op1,s1)` >>
  Cases_on `lower_value compile_expr ce fty e2 s1` >>
  rename1 `_ = (op2,s2)` >>
  `cs_extends sa s1 /\ cs_extends s1 s2` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  `for_range_checked_code ce lctx
      (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
      id fty bound stmts op1 op2 s2 = ((),sb)` by
    (qpat_assum `lower_value _ _ _ e1 sa = _`
       (mp_then Any mp_tac compile_stmt_for_range_checked) >>
     disch_then drule >> simp[] >> metis_tac[]) >>
  `cs_extends sa s2` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  fs[] >>
  `cs_extends s2 sb` by
    (drule for_range_checked_parts >>
     disch_then (qspecl_then [`sa`, `fp.jc_func`] mp_tac) >>
     (impl_tac >- metis_tac[]) >> metis_tac[]) >>
  `fn_has_code sa s2 fp.jc_func /\ fn_has_code s2 sb fp.jc_func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code sa s1 fp.jc_func /\ fn_has_code s1 s2 fp.jc_func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `supported_expr fp.jc_tops e1 /\ supported_expr fp.jc_tops e2` by
    simp[supported_expr_def] >>
  `expr_body_pre ce fp.jc_cx env e1 es` by
    (irule bodyExprPreFactsTheory.stmt_expr_body_pre >>
     fs[intcall_joint_res_def, intcall_expr_res_def, stmt_exprs_ok_def,
        supported_stmt_expr_exists_def, allocLimitsTheory.alloc_limits_stmt_def] >>
     qpat_assum `supported_expr _ e1`
       (strip_assume_tac o MATCH_MP bodyExprPreFactsTheory.supported_expr_body_calls) >>
     fs[body_inv_def, gasContextTheory.cx_tops_def,
        supported_iterator_exists_def, AllCaseEqs()] >>
     qexists_tac `[]` >> simp[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
     fs[intcall_frame_ok_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr fp.jc_cx e1) (read_result fp.jc_cx))
     expr_res_ok es` by metis_tac[expr_body_pre_gas_admissible] >>
  `intcall_expr_res fp ce env es sa s` by fs[intcall_joint_res_def] >>
  `intcall_forced_producer fp e1` by metis_tac[] >>
  qpat_x_assum `intcall_forced_producer fp e1`
    (mp_tac o REWRITE_RULE [intcall_forced_producer_def]) >>
  disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`env`, `es`, `s`] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  `eval_stmt fp.jc_cx (For id fty (Range e1 e2) bound stmts) =
   bind (bind (eval_expr fp.jc_cx e1) (read_result fp.jc_cx)) (\v1.
   bind (bind (eval_expr fp.jc_cx e2) (read_result fp.jc_cx)) (\v2.
   bind (lift_sum (get_range_limits v1 v2)) (\rl.
   bind (check (compatible_bound (Dynamic bound) (SND rl)) "For too long") (\u.
   eval_for fp.jc_cx tyv id stmts
     (GENLIST (\j. IntV (FST rl + &j)) (SND rl))))))` by
    (simp[Once evaluate_def, LET_THM, lift_option_type_def] >>
     simp[Once evaluate_def, ignore_bind_def, bind_assoc, bind_return, LENGTH_GENLIST]) >>
  pop_assum SUBST_ALL_TAC >>
  irule stmtReasonVvMemoryTheory.gas_outcome_bind_value >>
  goal_assum (drule_at Any) >>
  reverse conj_tac
  >- (rpt strip_tac >> Cases_on `res` >>
      fs[exprSimDefsTheory.expr_exit_INL, stmtSimPropsTheory.expr_exit_INR_type,
         intcall_stmt_exit_def]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `expr_body_pre ce fp.jc_cx env e2 (mid with gas_obs := [])` by
    (irule bodyExprPreFactsTheory.stmt_expr_body_pre >>
     fs[intcall_expr_cont_def, intcall_expr_res_def, stmt_exprs_ok_def,
        supported_stmt_expr_exists_def, allocLimitsTheory.alloc_limits_stmt_def] >>
     qpat_assum `supported_expr _ e2`
       (strip_assume_tac o MATCH_MP bodyExprPreFactsTheory.supported_expr_body_calls) >>
     fs[body_inv_def, gasContextTheory.cx_tops_def,
        supported_iterator_exists_def, AllCaseEqs()] >>
     qexists_tac `[]` >> simp[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
     fs[intcall_frame_ok_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr fp.jc_cx e2) (read_result fp.jc_cx))
     expr_res_ok (mid with gas_obs := [])` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `intcall_forced_producer fp e2` by metis_tac[] >>
  qpat_x_assum `intcall_forced_producer fp e2`
    (mp_tac o REWRITE_RULE [intcall_forced_producer_def]) >>
  disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`env`, `mid with gas_obs := []`, `t`] mp_tac) >>
  (impl_tac >- fs[intcall_expr_cont_def]) >> strip_tac >>
  irule stmtReasonVvMemoryTheory.gas_outcome_bind_value >>
  goal_assum (drule_at Any) >>
  reverse conj_tac
  >- (rpt strip_tac >> Cases_on `res` >>
      fs[exprSimDefsTheory.expr_exit_INL, stmtSimPropsTheory.expr_exit_INR_type,
         intcall_stmt_exit_def]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `expr_type e1 = expr_type e2` by
    (drule (SIMP_RULE std_ss [pairTheory.FORALL_PROD]
      (CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX)))
        bodySimDeclCasesTheory.body_range_typing)) >>
     (impl_tac >- metis_tac[]) >> metis_tac[]) >>
  `?n1. v = IntV n1 /\ value_has_type tyv (IntV n1)` by
    (irule marked_forced_integer_typed >>
     qpat_assum `gas_marked_exec _ _ _ (es,s) _ _ _ _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `?n2. v' = IntV n2 /\ value_has_type tyv (IntV n2)` by
    (irule marked_forced_integer_typed >>
     qpat_assum `gas_marked_exec _ _ _ (mid with gas_obs := [],t) _ _ _ _`
       (irule_at Any) >> simp[] >> metis_tac[expr_body_pre_gas_obs]) >>
  gvs[] >>
  `is_word_type (expr_type e2)` by
    (Cases_on `expr_type e2` >> gvs[is_int_type_def] >>
     rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_int_type_def, is_word_type_def]) >>
  `eval_operand op1 t = SOME (i2w n1) /\
   eval_operand op2 t' = SOME (i2w n2)` by
    (fs[expr_val_rel_def] >>
     metis_tac[exprSimPropsTheory.typed_val_to_w256_word_value,
       loweringSliceTheory.word_value_def, valueEncodingTheory.val_to_w256_def]) >>
  `(!z. op1 = Var z ==> not_fresh_at s1 z) /\ (!l. op1 <> Label l)` by
    (qpat_assum `lower_value _ _ _ e1 sa = _`
       (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
     simp[] >> metis_tac[]) >>
  `eval_operand op1 t' = SOME (i2w n1)` by
    (qpat_assum `intcall_expr_cont _ _ _ _ s1 t _ _ _` mp_tac >>
     pure_rewrite_tac[intcall_expr_cont_def] >> strip_tac >>
     Cases_on `op1` >> gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `intcall_joint_res fp ce env (mid' with gas_obs := []) sa t'` by
    (irule intcall_joint_res_reentry >>
     `local_ptrs_reserved ce sa /\
      (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at sa x)` by
       fs[intcall_joint_res_def, intcall_expr_res_def] >>
     simp[] >> qexists_tac `s2` >>
     fs[intcall_joint_res_def, intcall_expr_cont_def]) >>
  qpat_assum `for_range_checked_code _ _ _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac intcall_for_checked_compiled_tail) >>
  disch_then (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand op1 _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand op2 _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `type_stmts _ _ _ = _`)) >>
  disch_then (drule_at (Pat `supported_stmts _ _ _`)) >>
  (impl_tac >- (
    `sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var` by
      metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
    fs[intcall_expr_cont_def] >>
    simp[] >>
    conj_tac >- metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
    conj_tac >- (
      `value_has_type tyv (IntV (&bound))` by
        (drule_all vyperTypeValuesTheory.well_typed_literal_sound >>
         simp[vyperValueOperationTheory.evaluate_literal_def]) >>
      `value_has_type tyv (IntV 0)` by
        (Cases_on `expr_type e2` >> gvs[is_int_type_def] >>
         rename1 `evaluate_type _ (BaseT bt) = _` >> Cases_on `bt` >>
         gvs[is_int_type_def, vyperValueTheory.evaluate_type_def,
             value_has_type_def, vyperValueTheory.within_int_bound_def]) >>
      drule_at (Pat `evaluate_type _ _ = _`) range_end_words >>
      disch_then (qspecl_then [`0`, `&bound`] mp_tac) >> simp[]) >>
    conj_tac >- (
      drule singleton_for_body_typing >>
      simp[extend_local_def]) >>
    conj_tac >- metis_tac[bodySimDeclCasesTheory.body_for_exprs_ok] >>
    strip_tac >>
    qpat_assum `gas_marked_exec _ _ _ (es,s) _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
    drule_all stmtSimForRoundsTheory.gas_admissible_bind_tail >>
    simp[] >> strip_tac >>
    qpat_assum `gas_marked_exec _ _ _ (mid with gas_obs := [],t) _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
    fs[] >>
    qpat_x_assum `!tail. bind (eval_expr _ e1) _ _ = _` kall_tac >>
    qpat_x_assum `gas_admissible (bind (bind (eval_expr _ e1) _) _) _ _` kall_tac >>
    drule_all stmtSimForRoundsTheory.gas_admissible_bind_tail >>
    simp[get_range_limits_def, vyperValueTheory.compatible_bound_def, lift_sum_def,
         check_def, assert_def, return_def, bind_def, gasContextTheory.gas_admissible_def])) >>
  strip_tac >> fs[ignore_bind_def] >>
  irule exprSimSubscriptMapTheory.gas_outcome_conseq >>
  qpat_assum `gas_outcome _ _ _ _ (mid' with gas_obs := [],t') _ _`
    (irule_at Any) >> simp[ignore_bind_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[stmt_lands_def, cenv_top_ext_refl] >>
  `env' = env` by
    (qpat_x_assum `type_stmt _ _ _ = SOME env'` mp_tac >>
     simp[Once type_stmt_def, AllCaseEqs()] >> metis_tac[]) >>
  `cs'.cs_current_insts = []` by
    (drule for_range_checked_parts >>
     disch_then (qspecl_then [`sa`, `fp.jc_func`] mp_tac) >>
     (impl_tac >- metis_tac[]) >> metis_tac[]) >>
  gvs[block_is_terminated_def] >>
  conj_tac
  >- (irule bodyIntCallJointStmtBoundaryTheory.intcall_joint_res_next_var >>
      qexists_tac `sa` >> simp[] >>
      qpat_assum `compile_stmt _ _ _ _ sa = _`
        (mp_then Any mp_tac
          (REWRITE_RULE [fragExecTheory.cs_mono_def]
            (cj 1 stmtLoweringMonoTheory.compile_stmt_cs_mono))) >>
      simp[]) >>
  fs[intcall_expr_cont_def] >>
  rpt strip_tac >>
  `sa.cs_next_var <= s1.cs_next_var` by
    (qpat_assum `lower_value _ _ _ e1 sa = _`
       (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
     simp[]) >>
  `not_fresh_at s1 x` by
    (irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  metis_tac[]
QED
