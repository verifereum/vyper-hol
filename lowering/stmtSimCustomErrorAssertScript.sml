Theory stmtSimCustomErrorAssert
Ancestors
  stmtSimIf stmtSimIfProps stmtSimAssertProps stmtSimProps stmtSimDefs exprSimDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext gasCount fragGasPath fragGasMode
  fragExec localPtrsProps loweringSlice exprLowering stmtLowering
  emitHelper emitHelperProps exprLoweringProps stmtLoweringMono compileEnv
  externalEntryShape venomExecSemantics venomState
  vyperInterpreter vyperState vyperValue vyperExprNoControl
  vyperValueOperation vyperStatePreservation list finite_map
Libs
  monadsyntax

Theorem eval_assert_custom_error_bind:
  eval_stmt cx (Assert e (AssertCustomError err)) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. if v = BoolV T then return ()
           else if v = BoolV F then eval_stmt cx (Raise (RaiseCustomError err))
           else raise (Error (TypeError "not BoolV")))
Proof
  simp[FUN_EQ_THM, Once evaluate_def, eval_expr_switch_forced] >>
  gen_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e x` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `read_result cx v st` >>
  Cases_on `read_result cx v st` >> rename1 `_ = (forced,sf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >>
  simp[Once evaluate_def, bind_def]
QED

Theorem compile_assert_custom_error_parts:
  stmt_env cenv lctx ty (Assert e (AssertCustomError err)) sa = (cenv',sb) ==>
  ?op s1 ok s2 fl s3 s4 entry last.
    cenv' = cenv /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
    fresh_label "assert_ok" s1 = (ok,s2) /\
    fresh_label "assert_fail" s2 = (fl,s3) /\
    emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
    new_block fl s4 = (s4.cs_current_bb,entry) /\
    stmt_env cenv lctx ty (Raise (RaiseCustomError err)) entry = (cenv,last) /\
    new_block ok last = (last.cs_current_bb,sb)
Proof
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr cenv (BaseT BoolT) e sa` >>
  rename1 `_ = (op,s1)` >> simp[] >>
  Cases_on `fresh_label "assert_ok" s1` >> rename1 `_ = (ok,s2)` >> simp[] >>
  Cases_on `fresh_label "assert_fail" s2` >> rename1 `_ = (fl,s3)` >> simp[] >>
  Cases_on `emit_inst JNZ [op; Label ok; Label fl] [] s3` >>
  rename1 `_ = (u,s4)` >> Cases_on `u` >> simp[] >>
  Cases_on `new_block fl s4` >> rename1 `_ = (v,entry)` >> simp[] >>
  Cases_on `compile_revert_with_custom_error cenv err entry` >>
  rename1 `_ = (u,last)` >> Cases_on `u` >> simp[] >>
  Cases_on `new_block ok last` >> rename1 `_ = (x,sb1)` >>
  simp[] >> strip_tac >> gvs[] >>
  imp_res_tac new_block_props >> gvs[]
QED

Theorem assert_custom_error_condition_admissible:
  gas_admissible (eval_stmt cx (Assert e (AssertCustomError err)))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx))
    (\r. expr_res_ok r /\ (!v. r = INL v ==> ?b. v = BoolV b)) es
Proof
  strip_tac >> pure_rewrite_tac[gas_admissible_def] >>
  rpt gen_tac >> disch_tac >>
  Cases_on `res`
  >- (rename1 `_ = (INL v,ee)` >> simp[expr_res_ok_def] >> rpt strip_tac >>
      Cases_on `v = BoolV T` >- metis_tac[] >>
      Cases_on `v = BoolV F` >- metis_tac[] >>
      `eval_stmt cx (Assert e (AssertCustomError err)) (es with gas_obs := gs) =
        (INR (Error (TypeError "not BoolV")),ee)` by
        simp[eval_assert_custom_error_bind, bind_def, raise_def] >>
      drule_all gas_admissible_result >> simp[stmt_res_ok_def]) >>
  rename1 `_ = (INR ex,ee)` >>
  `no_control_exc ex` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
     rename1 `_ = (raw,st)` >> Cases_on `raw` >> simp[] >>
     metis_tac[read_result_no_control, cj 1 eval_expr_no_control]) >>
  `eval_stmt cx (Assert e (AssertCustomError err)) (es with gas_obs := gs) =
    (INR ex,ee)` by simp[eval_assert_custom_error_bind, bind_def] >>
  drule_all gas_admissible_result >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

Theorem assert_custom_error_raise_admissible:
  gas_admissible (eval_stmt cx (Assert e (AssertCustomError err)))
    (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV F),mid with gas_obs := tail)) ==>
  gas_admissible (eval_stmt cx (Raise (RaiseCustomError err)))
    (stmt_res_ok lctx) (mid with gas_obs := [])
Proof
  strip_tac >> simp[gas_admissible_def] >> rpt strip_tac >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `xs ++ gs` mp_tac) >>
  simp[eval_assert_custom_error_bind, bind_def] >> metis_tac[]
QED

Theorem compile_raise_custom_error_extends:
  stmt_env cenv lctx ty (Raise (RaiseCustomError err)) sa = (cenv',sb) ==>
  cs_extends sa sb
Proof
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_revert_with_custom_error cenv err sa` >>
  rename1 `_ = (u,last)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  mp_tac (cj 2 externalEntryShapeTheory.compile_custom_error_labels) >>
  disch_then (qspecl_then [`cenv`,`err`,`sa`] mp_tac) >> simp[]
QED

Theorem compile_raise_custom_error_ci_mono:
  stmt_env cenv lctx ty (Raise (RaiseCustomError err)) sa = (cenv',sb) ==>
  ci_mono sa sb
Proof
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_revert_with_custom_error cenv err sa` >>
  rename1 `_ = (unit,last_state)` >> Cases_on `unit` >>
  simp[] >> strip_tac >> gvs[] >>
  mp_tac (cj 2 ci_mono_custom_error) >>
  disch_then (qspecl_then [`cenv`,`err`,`sa`] mp_tac) >> simp[]
QED

Theorem assert_custom_error_compiler_code:
  lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
  fresh_label "assert_ok" s1 = (ok,s2) /\
  fresh_label "assert_fail" s2 = (fl,s3) /\
  emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
  new_block fl s4 = (x5,entry) /\
  stmt_env cenv lctx ty (Raise (RaiseCustomError err)) entry = (cenv,last) /\
  new_block ok last = (x7,sb) /\ fn_has_code sa sb func ==>
  fn_has_code sa s1 func /\ fn_has_code entry last func /\
  lookup_block s4.cs_current_bb func.fn_blocks =
    SOME <| bb_label := s4.cs_current_bb; bb_instructions := s4.cs_current_insts |> /\
  s3.cs_current_bb = s1.cs_current_bb /\
  s3.cs_current_insts = s1.cs_current_insts /\
  entry.cs_current_bb = fl /\ entry.cs_current_insts = [] /\
  sb.cs_current_bb = ok /\ sb.cs_current_insts = [] /\
  sa.cs_next_var <= entry.cs_next_var
Proof
  strip_tac >> drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_raise_custom_error_extends >> strip_tac >>
  imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
  `cs_extends s1 s2 /\ cs_extends s2 s3 /\ cs_extends s3 s4 /\
   cs_extends s4 entry /\ cs_extends last sb` by
    metis_tac[cs_extends_fresh_label, cs_extends_new_block,
              cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code s4 entry func` by
    metis_tac[fn_has_code_split, fn_has_code_mid, cs_extends_trans,
              cs_extends_refl] >>
  drule_all fn_has_code_new_block >> strip_tac >>
  simp[] >>
  conj_tac
  >- metis_tac[fn_has_code_split, cs_extends_trans] >>
  conj_tac
  >- metis_tac[fn_has_code_mid, cs_extends_trans] >>
  `s3.cs_next_var = s4.cs_next_var` by
    metis_tac[emit_inst_extends] >>
  decide_tac
QED

Theorem cond_jump_expr_post_frag[local]:
  !ctx func cx cenv e es sa op s1 s3 s4 lt lf s0.
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
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
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (bind (eval_expr cx e) (read_result cx)) (es,s0)
      (\res ee t. ?b u.
        res = INL (BoolV b) /\ t = jump_to (if b then lt else lf) u /\
        ~u.vs_halted /\
        expr_post ctx func cenv cx e es sa s1 s0 ee (BoolV b) op u)
      (\res ee r. expr_exit res r)
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`,`s1`,`op`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "path"
  >- (qexists_tac `marks` >> disj1_tac >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED
Resume cond_jump_expr_post_frag[path]:
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
  `gas_marked_path F ctx func s0 (LENGTH marks) (OK t)` by
    fs[gas_marked_exec_def] >>
  `~t.vs_halted` by
    (fs[gas_marked_path_def] >> metis_tac[gas_path_normal]) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    (drule_all if_condition_operand >> Cases_on `b` >>
     simp[valueEncodingTheory.val_to_w256_def]) >>
  drule emit_inst_extends >> strip_tac >>
  `fn_has_code s3 s4 func` by
    gvs[fn_has_code_def, emitted_blocks_def] >>
  `gas_path ctx func t 0 (OK (jump_to (if b then lt else lf) t))` by
    (irule assert_jnz_zero_path >> simp[] >>
     qexistsl_tac [`op`,`s3`,`s4`] >> gvs[]) >>
  `gas_marked_path F ctx func s0 (LENGTH marks)
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
Finalise cond_jump_expr_post_frag

Theorem eval_raise_custom_error_non_normal:
  eval_stmt cx (Raise (RaiseCustomError err)) es = (res,ee) ==>
  ?ex. res = INR ex /\ no_control_exc ex
Proof
  Cases_on `err` >> simp[Once evaluate_def] >>
  Cases_on `get_module_code cx (FST p)` >> simp[raise_def, no_control_exc_def] >>
  Cases_on `lookup_custom_error_args_in (SND p) x` >> simp[raise_def, no_control_exc_def] >>
  Cases_on `order_custom_error_args x' (CustomError p l l0)` >> simp[raise_def, no_control_exc_def] >>
  simp[bind_def] >>
  Cases_on `eval_exprs cx x'' es` >>
  rename1 `eval_exprs cx x'' es = (raw,st)` >>
  reverse (Cases_on `raw`)
  >- (simp[] >> strip_tac >> gvs[] >> metis_tac[cj 2 eval_expr_no_control, no_control_exc_def]) >>
  simp[] >> rename1 `eval_exprs cx x'' es = (INL vs,st)` >>
  simp[lift_option_def, raise_def, return_def] >>
  Cases_on `build_custom_error_data (get_tenv cx) (SND p) (MAP SND x') vs` >>
  simp[raise_def, return_def, no_control_exc_def] >> strip_tac >> gvs[]
QED

Theorem compile_assert_custom_error_frag_general:
  !ctx func cx lctx RetQ cenv ty e err es.
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!gs es1.
       (do raw <- eval_expr cx e; read_result cx raw od)
         (es with gas_obs := gs) = (INL (BoolV F),es1) ==>
       stmt_frag ctx func cx lctx RetQ cenv
         (stmt_env cenv lctx ty (Raise (RaiseCustomError err)))
         (eval_stmt cx (Raise (RaiseCustomError err))) es1) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertCustomError err)))
      (eval_stmt cx (Assert e (AssertCustomError err))) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `stmt_env _ _ _ _ _ = _`) compile_assert_custom_error_parts >>
  strip_tac >> gvs[] >>
  drule_all assert_custom_error_compiler_code >> strip_tac >>
  drule assert_custom_error_condition_admissible >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
   gas_admissible (bind (eval_expr cx e) (read_result cx))
     (\r. !v. r = INL v ==> ?b. v = BoolV b) es` by
    (gvs[gas_admissible_def] >> metis_tac[]) >>
  drule_all cond_jump_expr_post_frag >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qpat_x_assum `?res es_end rr. _` strip_assume_tac >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  suspend "cert"
QED

Resume compile_assert_custom_error_frag_general[exception]:
  Cases_on `res` >- fs[expr_exit_def] >>
  rename1 `expr_exit (INR ex) rr` >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR ex`, `es_end`, `rr`] >> conj_tac
  >- (rewrite_tac[eval_assert_custom_error_bind] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_assert_custom_error_frag_general[cert]:
  qexists_tac `marks` >> disj2_tac >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`err'`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_assert_custom_error_bind] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

Resume compile_assert_custom_error_frag_general[normal]:
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL (BoolV b),es_end with gas_obs := tail)` by
    gvs[gas_marked_exec_def] >>
  Cases_on `b` >- suspend "true" >> suspend "false"
QED

Resume compile_assert_custom_error_frag_general[true]:
  gvs[] >> qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INL ()`,`es_end`,`OK (jump_to sb.cs_current_bb u)`] >>
  conj_tac
  >- (simp[gas_marked_exec_def] >> conj_tac
      >- simp[eval_assert_custom_error_bind, Once bind_def, return_def] >>
      gvs[gas_marked_exec_def]) >>
  disj1_tac >> simp[] >> irule assert_success_post >> simp[] >>
  conj_tac
  >- (qpat_x_assum `!tail. _` (qspec_then `[]` assume_tac) >>
      drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
  qexistsl_tac [`e`,`op`,`s1`] >> simp[]
QED
Resume compile_assert_custom_error_frag_general[false]:
  gvs[] >>
  `gas_admissible (eval_stmt cx (Raise (RaiseCustomError err)))
    (stmt_res_ok lctx) (es_end with gas_obs := [])` by
    (irule assert_custom_error_raise_admissible >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `stmt_frag ctx func cx lctx RetQ cenv
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
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >>
  disch_then drule >> simp[block_is_terminated_def] >>
  disch_then (qspec_then `jump_to entry.cs_current_bb u` mp_tac) >>
  (impl_tac >- gvs[stmt_state_rel_jump_to, jump_to_def, expr_post_def]) >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "false_normal"
  >- suspend "false_exit"
  >> suspend "false_cert"
QED
Resume compile_assert_custom_error_frag_general[false_normal]:
  gvs[gas_marked_exec_def] >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
  strip_tac >> drule eval_raise_custom_error_non_normal >>
  gvs[stmt_post_def, stmt_lands_def, AllCaseEqs(), no_control_exc_def]
QED
Resume compile_assert_custom_error_frag_general[false_exit]:
  rename1 `exit_result rr` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  qexistsl_tac [`res`,`es_end'`,`rr`] >> simp[] >>
  reverse conj_tac >- (disj2_tac >> gvs[]) >>
  rewrite_tac[eval_assert_custom_error_bind] >>
  irule gas_marked_exec_bind_normal >>
  qexistsl_tac [`es_end`,`jump_to entry.cs_current_bb u`,`BoolV F`] >> simp[]
QED
Resume compile_assert_custom_error_frag_general[false_cert]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  qexistsl_tac [`err'`,`ee`,`leaf`,`finish'`] >>
  rewrite_tac[eval_assert_custom_error_bind] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  qexistsl_tac [`es_end`,`jump_to entry.cs_current_bb u`,`BoolV F`] >>
  simp[GSYM ignore_bind_def]
QED
Finalise compile_assert_custom_error_frag_general
