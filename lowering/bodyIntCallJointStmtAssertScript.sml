(* Assertions with a control-only successful suffix. *)
Theory bodyIntCallJointStmtAssert
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtBoundary bodyIntCallJointStmtJump
  bodyIntCallJointStmtSeq stmtSimAssertProps stmtSimIfProps stmtSimProps
  bodyExprPreFacts bodySim exprSimSource exprSimDefs exprSimHypsDefs
  loweringPosts stmtSimDefs stmtLowering exprLowering exprLoweringProps
  compileEnv emitHelper emitHelperProps placeMemoryCodeLayout supportedStmts supportedStmtTraverse
  supportedExprs supportedExprTraverse allocLimits vyperTypeSystem
  vyperTypeCallGraph vyperTypeCallStackSoundness
  gasOutcome gasSummary gasContext fragGasMode fragGasPath fragExec
  vyperInterpreter vyperState vyperValue venomState venomInst venomExecSemantics
  valueEncoding list finite_map

Theorem intcall_stmts_producer_assert:
  !fp e ak. (ak = AssertBare \/ ak = AssertUnreachable) /\
    intcall_forced_producer fp e ==>
    intcall_stmts_producer fp [Assert e ak]
Proof
  rpt gen_tac >> strip_tac >> (
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  gvs[stmts_env_singleton] >>
  drule_at (Pat `stmt_env _ _ _ _ _ = _`) compile_assert_parts >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
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
  drule_all assert_compiler_code >> strip_tac >>
  `gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
     expr_res_ok es` by metis_tac[assert_expr_admissible] >>
  imp_res_tac (GEN_ALL (DISCH_ALL (CONJUNCT1 (UNDISCH
    (iffLR (SPEC_ALL intcall_joint_res_def)))))) >>
  qpat_x_assum `intcall_forced_producer _ _`
    (mp_tac o REWRITE_RULE [intcall_forced_producer_def]) >>
  disch_then drule_all >> strip_tac >>
  pop_assum mp_tac >> simp[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `?res ee r. _` strip_assume_tac >> gvs[]
      >- suspend "normal" >> suspend "exit") >>
  qexists_tac `marks` >> disj2_tac >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule assert_expr_exempt >> simp[])
QED

Resume intcall_stmts_producer_assert[exit]:
  markerLib.RESUME_TAC >> (
  Cases_on `res` >- fs[expr_exit_def] >> rename1 `expr_exit (INR ex) r` >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >>
  conj_tac
  >- (fs[gas_marked_exec_def] >> gen_tac >>
      asm_simp_tac (srw_ss()) [eval_assert_bind] >> simp[Once bind_def]) >>
  disj2_tac >> simp[intcall_stmt_exit_def] >>
  metis_tac[expr_exit_INR_type])
QED

Resume intcall_stmts_producer_assert[normal]:
  markerLib.RESUME_TAC >> (
  qmatch_goalsub_abbrev_tac `eval_stmt cx (Assert e ak)` >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
  `?b. v = BoolV b` by
    (Cases_on `eval_stmt cx (Assert e ak)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings)` >>
     drule_all gas_admissible_result >> strip_tac >>
     drule_at (Pat `eval_stmt _ _ _ = _`) eval_assert_forced_ok >>
     disch_then (qspec_then `lctx` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_x_assum `!tail. _ = _` (qspec_then `[]` assume_tac) >>
     gvs[bind_def]) >>
  `eval_operand op u = SOME (if b then 1w else 0w)` by
    gvs[expr_val_rel_def, evaluate_type_def, is_word_type_def,
        typed_val_to_w256_def, val_to_w256_def] >>
  `gas_path fp.jc_ctx fp.jc_func u 0
     (OK (jump_to (if b then sb.cs_current_bb else s5.cs_current_bb) u))` by
    (imp_res_tac emit_inst_extends >>
     irule assert_jnz_zero_path >> fs[intcall_expr_cont_def] >>
     qexistsl_tac [`op`, `s3`, `s4`] >> simp[]) >>
  Cases_on `b` >- suspend "true" >> suspend "false")
QED

Resume intcall_stmts_producer_assert[false]:
  markerLib.RESUME_TAC >> (
  gvs[] >>
  `?a t. step_inst_base
      (mk_inst s5.cs_next_id (if ak = AssertBare then REVERT else INVALID)
        (if ak = AssertBare then [Lit 0w; Lit 0w] else []) [])
      (jump_to s5.cs_current_bb u) = Abort a t /\
      expr_exit (INR (AssertException
        (if ak = AssertBare then "" else "UNREACHABLE")) : unit + exception)
        (Abort a t)` by
    (simp[Abbr `ak`, expr_exit_def] >>
     metis_tac[step_revert_zero, step_invalid]) >>
  `gas_path fp.jc_ctx fp.jc_func (jump_to s5.cs_current_bb u) 0 (Abort a t)` by
    (irule emit_abort_zero_path >> fs[jump_to_def, intcall_expr_cont_def] >>
     qexistsl_tac [`if ak = AssertBare then REVERT else INVALID`,
                   `if ak = AssertBare then [Lit 0w; Lit 0w] else []`, `s5`, `s6`] >>
     gvs[jump_to_def, Abbr `ak`]) >>
  qexistsl_tac [`INR (AssertException
      (if ak = AssertBare then "" else "UNREACHABLE"))`, `es_end`, `Abort a t`] >>
  conj_tac
  >- (conj_tac
      >- (gen_tac >> simp[Abbr `ak`, eval_assert_bind] >>
          simp[Once bind_def, raise_def]) >>
      metis_tac[gas_path_then, arithmeticTheory.ADD_CLAUSES]) >>
  disj2_tac >> simp[exit_result_def, intcall_stmt_exit_def])
QED

Resume intcall_stmts_producer_assert[true]:
  markerLib.RESUME_TAC >> (
  imp_res_tac fresh_label_next_var >>
  imp_res_tac emit_inst_next_var >>
  imp_res_tac new_block_next_var >>
  gvs[] >>
  qexistsl_tac [`INL ()`, `es_end`, `OK (jump_to sb.cs_current_bb u)`] >>
  conj_tac
  >- (conj_tac
      >- (gen_tac >> asm_simp_tac (srw_ss()) [eval_assert_bind] >>
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
       cenv_top_ext_refl, lookup_var_def, block_is_terminated_def])
QED

Finalise intcall_stmts_producer_assert
