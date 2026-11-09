(* Reason assertions compose a forced condition with a Raise producer. *)
Theory bodyIntCallFamStmtExitAssert
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtBoundary bodyIntCallJointStmtJump
  bodyIntCallJointStmtSeq stmtSimAssertProps stmtSimIfProps stmtSimProps
  stmtSimReason stmtReasonVvMemory bodyExprPreFacts bodySim exprSimSource
  exprSimDefs exprSimHypsDefs loweringPosts stmtSimDefs stmtLowering exprLowering
  exprLoweringProps compileEnv emitHelper emitHelperProps placeMemoryCodeLayout
  supportedStmts supportedStmtTraverse supportedExprs supportedExprTraverse
  allocLimits vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  gasOutcome gasSummary gasContext gasSummaryCompose gasSummaryComposePtr
  gasExemptCert stmtSimReasonExpr fragGasMode fragGasPath fragExec
  vyperInterpreter vyperState vyperValue venomState venomInst venomExecSemantics
  valueEncoding vyperExprNoControl list finite_map

Theorem intcall_stmts_producer_assert_reason:
  intcall_forced_producer fp e /\
  intcall_stmts_producer fp [Raise (RaiseReason r)] ==>
  intcall_stmts_producer fp [Assert e (AssertReason r)]
Proof
  strip_tac >>
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >> gvs[stmts_env_singleton] >>
  drule_at (Pat `stmt_env _ _ _ _ _ = _`) compile_assert_reason_raise_parts >>
  strip_tac >> gvs[] >>
  gvs[supported_stmt_def, type_stmt_def, int_calls_stmt_def,
      supported_stmt_expr_exists_def, AllCaseEqs()] >>
  `supported_expr fp.jc_tops e` by simp[supported_expr_def] >>
  `expr_body_pre ce fp.jc_cx env e es` by
    (irule stmt_expr_body_pre >>
     fs[intcall_joint_res_def, intcall_expr_res_def, stmt_exprs_ok_def,
        supported_stmt_expr_exists_def, alloc_limits_stmt_def] >>
     drule supported_expr_body_calls >> strip_tac >>
     fs[body_inv_def, cx_tops_def, AllCaseEqs()] >>
     qexists_tac `[]` >> simp[call_evaluation_safe_def] >>
     fs[intcall_frame_ok_def] >> metis_tac[]) >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  drule_all assert_reason_compiler_code >> strip_tac >>
  `gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
     expr_res_ok es` by metis_tac[assert_reason_expr_admissible] >>
  imp_res_tac (GEN_ALL (DISCH_ALL (CONJUNCT1 (UNDISCH
    (iffLR (SPEC_ALL intcall_joint_res_def)))))) >>
  qpat_x_assum `intcall_forced_producer _ _`
    (mp_tac o REWRITE_RULE [intcall_forced_producer_def]) >>
  disch_then drule_all >> strip_tac >>
  pop_assum mp_tac >> simp[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qpat_x_assum `?res ee rr. _` strip_assume_tac >> gvs[]
      >- suspend "normal" >> suspend "exit") >>
  qexists_tac `marks` >> disj2_tac >>
  metis_tac[assert_reason_expr_exempt]
QED

Resume intcall_stmts_producer_assert_reason[exit]:
  qexists_tac `marks` >> disj1_tac >>
  Cases_on `res` >- fs[expr_exit_def] >>
  rename1 `expr_exit (INR ex) rr` >>
  qexistsl_tac [`INR ex`, `es_end`, `rr`] >> conj_tac
  >- (fs[gas_marked_exec_def] >> gen_tac >>
      asm_simp_tac (srw_ss()) [stmtReasonVvMemoryTheory.eval_assert_reason_bind] >>
      simp[Once bind_def]) >>
  disj2_tac >> simp[intcall_stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Resume intcall_stmts_producer_assert_reason[normal]:
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
  `?b. v = BoolV b` by
    (Cases_on `eval_stmt fp.jc_cx (Assert e (AssertReason r))
       (es with gas_obs := gas_explicit marks s.vs_gas_readings)` >>
     drule_all gas_admissible_result >> strip_tac >>
     qpat_x_assum `!tail. _ = _` (qspec_then `[]` assume_tac) >>
     gvs[stmtReasonVvMemoryTheory.eval_assert_reason_bind, bind_def] >>
     Cases_on `v` >>
     qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
     simp[return_def, raise_def] >> strip_tac >> gvs[stmt_res_ok_def]) >>
  `eval_operand op u = SOME (if b then 1w else 0w)` by
    gvs[expr_val_rel_def, evaluate_type_def, is_word_type_def,
        typed_val_to_w256_def, val_to_w256_def] >>
  `gas_path fp.jc_ctx fp.jc_func u 0
     (OK (jump_to (if b then sb.cs_current_bb else entry.cs_current_bb) u))` by
    (imp_res_tac emit_inst_extends >>
     irule assert_jnz_zero_path >> fs[intcall_expr_cont_def] >>
     qexistsl_tac [`op`, `s3`, `s4`] >> simp[]) >>
  Cases_on `b` >- suspend "true" >> suspend "false"
QED

Resume intcall_stmts_producer_assert_reason[true]:
  imp_res_tac fresh_label_next_var >> imp_res_tac emit_inst_next_var >>
  imp_res_tac new_block_next_var >> gvs[] >>
  `s1.cs_next_var <= sb.cs_next_var` by
    (`local_ptrs_reserved ce entry` by
       (irule local_ptrs_reserved_next_var >> qexists_tac `s1` >>
        fs[intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def]) >>
     qpat_assum `stmt_env _ _ _ (Raise _) _ = _`
       (mp_then Any mp_tac stmt_env_reserved) >>
     simp[stmtLoweringMonoTheory.compile_stmt_cs_mono] >>
     strip_tac >> decide_tac) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INL ()`, `es_end`, `OK (jump_to sb.cs_current_bb u)`] >>
  conj_tac
  >- (conj_tac
      >- (gen_tac >> asm_simp_tac (srw_ss())
            [stmtReasonVvMemoryTheory.eval_assert_reason_bind] >>
          simp[Once bind_def, return_def]) >>
      metis_tac[gas_path_then, arithmeticTheory.ADD_CLAUSES]) >>
  disj1_tac >> simp[] >>
  `intcall_joint_res fp ce env (es_end with gas_obs := []) sb u` by
    (fs[intcall_expr_cont_def] >>
     imp_res_tac (GEN_ALL (DISCH_ALL (CONJUNCT2 (UNDISCH
       (iffLR (SPEC_ALL intcall_joint_res_def)))))) >>
     imp_res_tac (GEN_ALL (iffRL (SPEC_ALL intcall_joint_res_def))) >>
     irule intcall_joint_res_next_var >>
     goal_assum (drule_at Any) >> simp[]) >>
  fs[intcall_expr_cont_def] >>
  simp[intcall_joint_res_jump_to, stmt_lands_def, jump_to_def,
       cenv_top_ext_refl, lookup_var_def, block_is_terminated_def]
QED

Resume intcall_stmts_producer_assert_reason[false]:
  gvs[] >>
  imp_res_tac fresh_label_next_var >> imp_res_tac emit_inst_next_var >>
  imp_res_tac new_block_next_var >>
  `intcall_joint_res fp ce env (es_end with gas_obs := []) entry
      (jump_to entry.cs_current_bb u)` by
    (simp[intcall_joint_res_jump_to] >>
     fs[intcall_expr_cont_def] >>
     imp_res_tac (GEN_ALL (DISCH_ALL (CONJUNCT2 (UNDISCH
       (iffLR (SPEC_ALL intcall_joint_res_def)))))) >>
     imp_res_tac (GEN_ALL (iffRL (SPEC_ALL intcall_joint_res_def))) >>
     irule intcall_joint_res_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `gas_admissible (eval_stmt fp.jc_cx (Raise (RaiseReason r)))
      (stmt_res_ok lctx) (es_end with gas_obs := [])` by
    (irule stmtReasonVvMemoryTheory.assert_reason_raise_admissible >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  qpat_x_assum `intcall_stmts_producer _ _`
    (mp_tac o REWRITE_RULE [intcall_stmts_producer_def, eval_stmts_singleton,
                            stmts_env_singleton]) >>
  disch_then (qspecl_then [`bindings`, `ce`, `ce`, `env`, `env`, `lctx`,
    `es_end with gas_obs := []`, `entry`, `last`,
    `jump_to entry.cs_current_bb u`] mp_tac) >>
  (impl_tac >- suspend "raise_pre") >>
  suspend "compose"
QED

Resume intcall_stmts_producer_assert_reason[raise_pre]:
  fs[supported_stmt_def, supported_raise_reason_def, supported_assert_reason_def,
     supported_stmt_expr_exists_def, supported_raise_exists_def,
     supported_assert_exists_def, type_stmt_def, int_calls_stmt_def,
     int_calls_raise_reason_def, int_calls_assert_reason_def,
     stmt_exprs_ok_def, alloc_limits_stmt_def, intcall_expr_cont_def,
     jump_to_def, block_is_terminated_def, AllCaseEqs()] >>
  gvs[stmts_env_singleton, alloc_limits_raise_def, alloc_limits_assert_def,
      compileVyperTheory.stmt_valued_return_def, AllCaseEqs()] >>
  `~block_is_terminated entry` by simp[block_is_terminated_def] >>
  simp[stmts_env_singleton] >>
  Cases_on `well_typed_expr (env with bare_global_assignable := FEMPTY) r` >>
  gvs[]
QED

Resume intcall_stmts_producer_assert_reason[compose]:
  `gas_marked_exec F (fp.jc_ctx,fp.jc_func)
     (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
     (es,s) marks (INL (BoolV F)) es_end
     (OK (jump_to entry.cs_current_bb u))` by
    (simp[gas_marked_exec_def, gas_marked_path_def] >>
     metis_tac[gas_path_then, arithmeticTheory.ADD_CLAUSES]) >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `right` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >- suspend "counted" >> suspend "counted_exit") >>
  strip_tac >> suspend "exempt"
QED

Resume intcall_stmts_producer_assert_reason[counted]:
  `stmt_res_ok lctx res` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     qpat_x_assum `!tail. eval_stmt _ (Raise _) _ = _`
       (qspec_then `[]` assume_tac) >>
     drule_all gas_admissible_result >> simp[]) >>
  `?rr. res = INR rr /\ no_control_exc rr` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     qpat_x_assum `!tail. eval_stmt _ (Raise _) _ = _`
       (qspec_then `[]` assume_tac) >>
     drule_all eval_raise_reason_cases >> strip_tac >>
     gvs[expr_res_ok_def, no_control_exc_def]) >>
  gvs[stmt_lands_def, no_control_exc_def]
QED

Resume intcall_stmts_producer_assert_reason[counted_exit]:
  `gas_marked_exec F (fp.jc_ctx,fp.jc_func)
     (eval_stmt fp.jc_cx (Assert e (AssertReason r)))
     (es,s) (marks ++ right) res es_end' r''` by
    (rewrite_tac[stmtReasonVvMemoryTheory.eval_assert_reason_bind] >>
     irule gas_marked_exec_bind_normal >>
     qexistsl_tac [`es_end`, `jump_to entry.cs_current_bb u`, `BoolV F`] >>
     simp[]) >>
  qexists_tac `marks ++ right` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end'`, `r''`] >>
  fs[gas_marked_exec_def, gas_marked_path_def]
QED

Resume intcall_stmts_producer_assert_reason[exempt]:
  qexists_tac `marks ++ right` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  pure_rewrite_tac[stmtReasonVvMemoryTheory.eval_assert_reason_bind,
                   ignore_bind_def] >>
  pure_once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  qexistsl_tac [`es_end`, `jump_to entry.cs_current_bb u`, `BoolV F`] >>
  simp[GSYM ignore_bind_def]
QED

Finalise intcall_stmts_producer_assert_reason
