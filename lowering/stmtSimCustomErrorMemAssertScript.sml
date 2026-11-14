(* Memory-checked conditional custom-error assertions. *)
Theory stmtSimCustomErrorMemAssert
Ancestors
  stmtSimCustomErrorAssert bodyMemoryDefs exprSimMemDefs allocaHistory
  stmtSimIf stmtSimIfProps stmtSimAssertProps stmtSimProps stmtSimDefs exprSimDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext gasCount fragGasPath fragGasMode
  fragGasPathMem fragExec localPtrsProps loweringSlice exprLowering stmtLowering
  emitHelper emitHelperProps exprLoweringProps stmtLoweringMono compileEnv
  externalEntryShape venomExecSemantics venomState
  vyperInterpreter vyperState vyperValue vyperExprNoControl
  vyperValueOperation vyperStatePreservation list finite_map
Libs
  monadsyntax

Theorem cond_jump_expr_post_frag_mem[local]:
  !ctx func cx cenv e es sa op s1 s3 s4 lt lf s0.
    expr_sim_mem ctx func cenv cx (BaseT BoolT) e es /\
    expr_type e = BaseT BoolT /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
    gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
    gas_admissible (bind (eval_expr cx e) (read_result cx))
      (\r. !v. r = INL v ==> ?b. v = BoolV b) es /\
    s3.cs_current_bb = s1.cs_current_bb /\
    s3.cs_current_insts = s1.cs_current_insts /\
    emit_inst JNZ [op; Label lt; Label lf] [] s3 = ((),s4) /\
    lookup_block s4.cs_current_bb func.fn_blocks =
      SOME <| bb_label := s4.cs_current_bb; bb_instructions := s4.cs_current_insts |> /\
    fn_has_code sa s1 func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome T (cx_tops cx) (ctx,func)
      (bind (eval_expr cx e) (read_result cx)) (es,s0)
      (\res ee t. ?b u.
        res = INL (BoolV b) /\ t = jump_to (if b then lt else lf) u /\
        ~u.vs_halted /\
        expr_post ctx func cenv cx e es sa s1 s0 ee (BoolV b) op u /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next)
      (\res ee r. expr_exit res r)
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`,`s1`,`op`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "path"
  >- (qexists_tac `marks` >> disj1_tac >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED
Resume cond_jump_expr_post_frag_mem[path]:
  gvs[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
   (INL v,es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `?b. v = BoolV b` by
    (qpat_x_assum `gas_admissible _ (\r. _) _` mp_tac >>
     rewrite_tac[gas_admissible_def] >> disch_then drule >> simp[]) >>
  gvs[] >>
  `gas_marked_path T ctx func s0 (LENGTH marks) (OK t)` by
    fs[gas_marked_exec_def] >>
  `~t.vs_halted` by
    (fs[gas_marked_path_def] >> metis_tac[gas_path_mem_exec, gas_path_normal]) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    (drule_all if_condition_operand >> Cases_on `b` >>
     simp[valueEncodingTheory.val_to_w256_def]) >>
  drule emit_inst_extends >> strip_tac >>
  `fn_has_code s3 s4 func` by
    gvs[fn_has_code_def, emitted_blocks_def] >>
  `gas_path_mem ctx func t 0 (OK (jump_to (if b then lt else lf) t))` by
    (irule assert_jnz_zero_path_mem >> simp[] >>
     qexistsl_tac [`op`,`s3`,`s4`] >> gvs[]) >>
  `gas_marked_path T ctx func s0 (LENGTH marks)
    (OK (jump_to (if b then lt else lf) t))` by
    (`LENGTH marks = LENGTH marks + 0` by simp[] >>
     pop_assum SUBST1_TAC >> irule gas_marked_path_then >>
     simp[gas_marked_path_def] >> metis_tac[gas_marked_path_def]) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INL (BoolV b)`,`es_end`,
                `OK (jump_to (if b then lt else lf) t)`] >>
  conj_tac >- fs[gas_marked_exec_def] >>
  disj1_tac >> simp[] >> qexists_tac `t` >> simp[]
QED
Finalise cond_jump_expr_post_frag_mem

Theorem compile_assert_custom_error_frag_general_mem:
  !d ctx func cx lctx RetQ cenv ty e err es.
    expr_type e = BaseT BoolT /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) e es /\
    (!gs es1.
       (do raw <- eval_expr cx e; read_result cx raw od)
         (es with gas_obs := gs) = (INL (BoolV F),es1) ==>
       stmt_frag_mem d ctx func cx lctx RetQ cenv
         (stmt_env cenv lctx ty (Raise (RaiseCustomError err)))
         (eval_stmt cx (Raise (RaiseCustomError err))) es1) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertCustomError err)))
      (eval_stmt cx (Assert e (AssertCustomError err))) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `stmt_env _ _ _ _ _ = _`) compile_assert_custom_error_parts >>
  strip_tac >> gvs[] >>
  drule_all assert_custom_error_compiler_code >> strip_tac >>
  drule assert_custom_error_condition_admissible >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
   gas_admissible (bind (eval_expr cx e) (read_result cx))
     (\r. !v. r = INL v ==> ?b. v = BoolV b) es` by
    (gvs[gas_admissible_def] >> metis_tac[]) >>
  drule_all cond_jump_expr_post_frag_mem >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qpat_x_assum `?res es_end rr. _` strip_assume_tac >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  suspend "cert"
QED

Resume compile_assert_custom_error_frag_general_mem[exception]:
  Cases_on `res` >- fs[expr_exit_def] >>
  rename1 `expr_exit (INR ex) rr` >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR ex`, `es_end`, `rr`] >> conj_tac
  >- (rewrite_tac[eval_assert_custom_error_bind] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_assert_custom_error_frag_general_mem[cert]:
  qexists_tac `marks` >> disj2_tac >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`err'`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_assert_custom_error_bind] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

Resume compile_assert_custom_error_frag_general_mem[normal]:
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL (BoolV b),es_end with gas_obs := tail)` by
    gvs[gas_marked_exec_def] >>
  Cases_on `b` >- suspend "true" >> suspend "false"
QED

Resume compile_assert_custom_error_frag_general_mem[true]:
  `sa.cs_next_var <= sb.cs_next_var` by
    (`ci_mono entry last` by
       metis_tac[compile_raise_custom_error_ci_mono] >>
     imp_res_tac new_block_props >> fs[ci_mono_def] >> decide_tac) >>
  qpat_x_assum `sa.cs_next_var <= entry.cs_next_var` kall_tac >>
  gvs[] >> qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INL ()`,`es_end`,`OK (jump_to sb.cs_current_bb u)`] >>
  conj_tac
  >- (simp[gas_marked_exec_def] >> conj_tac
      >- simp[eval_assert_custom_error_bind, Once bind_def, return_def] >>
      gvs[gas_marked_exec_def]) >>
  disj1_tac >> drule_all assert_success_post_mem >> simp[]
QED
Resume compile_assert_custom_error_frag_general_mem[false]:
  gvs[] >>
  `gas_admissible (eval_stmt cx (Raise (RaiseCustomError err)))
    (stmt_res_ok lctx) (es_end with gas_obs := [])` by
    (irule assert_custom_error_raise_admissible >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Raise (RaiseCustomError err)))
    (eval_stmt cx (Raise (RaiseCustomError err))) (es_end with gas_obs := [])` by
    (qpat_x_assum `!gs es1. _` irule >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
     qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `local_ptrs_reserved cenv entry` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `ret_pc_ok cenv entry (jump_to entry.cs_current_bb u)` by
    (simp[ret_pc_ok_jump_to] >> irule ret_pc_ok_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> gvs[expr_post_def]) >>
  `return_buf_frame d cenv entry (jump_to entry.cs_current_bb u)` by
    (simp[return_buf_frame_jump_to] >> irule return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> gvs[expr_post_def]) >>
  `alloca_history func (jump_to entry.cs_current_bb u)` by
    gvs[alloca_history_def, jump_to_def] >>
  qpat_x_assum `stmt_frag_mem _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_mem_def] >>
  disch_then drule >> simp[block_is_terminated_def] >>
  disch_then (qspec_then `jump_to entry.cs_current_bb u` mp_tac) >>
  (impl_tac >- gvs[stmt_state_rel_jump_to, jump_to_def, expr_post_def]) >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "false_normal"
  >- suspend "false_exit"
  >> suspend "false_cert"
QED
Resume compile_assert_custom_error_frag_general_mem[false_normal]:
  gvs[gas_marked_exec_def] >>
  qpat_x_assum `!tail. eval_stmt _ (Raise _) _ = _`
    (qspec_then `[]` mp_tac) >> simp[] >>
  strip_tac >> drule eval_raise_custom_error_non_normal >>
  gvs[stmt_post_def, stmt_lands_def, AllCaseEqs(), no_control_exc_def]
QED
Resume compile_assert_custom_error_frag_general_mem[false_exit]:
  rename1 `exit_result rr` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  qexistsl_tac [`res`,`es_end'`,`rr`] >> simp[] >>
  reverse conj_tac >- (disj2_tac >> gvs[]) >>
  rewrite_tac[eval_assert_custom_error_bind] >>
  irule gas_marked_exec_bind_normal >>
  qexistsl_tac [`es_end`,`jump_to entry.cs_current_bb u`,`BoolV F`] >> simp[]
QED
Resume compile_assert_custom_error_frag_general_mem[false_cert]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  qexistsl_tac [`err'`,`ee`,`leaf`,`finish'`] >>
  rewrite_tac[eval_assert_custom_error_bind] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  qexistsl_tac [`es_end`,`jump_to entry.cs_current_bb u`,`BoolV F`] >>
  simp[GSYM ignore_bind_def]
QED
Finalise compile_assert_custom_error_frag_general_mem
