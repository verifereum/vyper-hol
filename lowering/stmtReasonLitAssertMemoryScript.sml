(* Counted memory-safe assert with a string literal reason: the condition's
   JNZ, then on its false edge the literal's buffer and the reason encoder
   (stmtReasonLitFragMemory), which run to their REVERT. *)
Theory stmtReasonLitAssertMemory
Ancestors
  stmtReasonLitFragMemory stmtReasonLitMemory stmtReasonMemory
  exprSimMemDefs bodyMemoryDefs fragGasPathMem stmtSimAssert instMemFrontier
  stmtSimDefs stmtSimProps stmtSimIfProps stmtSimAssertProps exprSimDefs
  exprSimProps loweringPosts gasOutcome gasSummary gasSummaryCompose
  gasContext gasCount gasExemptCert fragGasPath fragGasMode
  list rich_list finite_map pred_set fragExec localPtrsProps loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding vyperInterpreter vyperState vyperValue
  vyperEvalPreservesScopes vyperExprNoControl vyperValueOperation
  vyperStatePreservation venomExecSemantics venomExecProofs venomInst
  venomState integer_word vyperAST context
Libs
  monadsyntax intLib

Theorem eval_lit_reason[local]:
  !cx ml str.
    (do stv <- eval_expr cx (Literal (BaseT (StringT ml)) (StringL str));
        sv <- read_result cx stv;
        s <- lift_option_type (dest_StringV sv) "not StringV";
        raise (AssertException s) od) = raise (AssertException str)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [FUN_EQ_THM] >> gen_tac >>
  simp_tac (srw_ss()) [Once evaluate_def, evaluate_literal_def, bind_def,
    return_def, read_result_def, lift_option_type_def, dest_StringV_def,
    raise_def]
QED

Theorem eval_assert_lit_bind:
  !cx e ml str.
    eval_stmt cx
      (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str)))) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. if v = BoolV T then return ()
           else if v = BoolV F then raise (AssertException str)
           else raise (Error (TypeError "not BoolV")))
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [FUN_EQ_THM] >> gen_tac >>
  simp_tac (srw_ss()) [Once evaluate_def] >>
  simp[eval_expr_switch_forced, eval_lit_reason] >>
  simp[bind_def] >>
  Cases_on `eval_expr cx e x` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `read_result cx v st` >>
  Cases_on `read_result cx v st` >> rename1 `_ = (forced,sf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem eval_assert_lit_forced_ok:
  !cx e ml str es res es' lctx.
    eval_stmt cx
      (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str))))
      es = (res, es') /\
    stmt_res_ok lctx res ==>
    ?r s. bind (eval_expr cx e) (read_result cx) es = (r,s) /\
      expr_res_ok r /\ (!v. r = INL v ==> ?b. v = BoolV b) /\
      (case r of INR ex => (INR ex,s)
       | INL v => if v = BoolV T then (INL (),s)
                  else if v = BoolV F then (INR (AssertException str),s)
                  else (INR (Error (TypeError "not BoolV")),s)) = (res,es')
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bind (eval_expr cx e) (read_result cx) es` >>
  rename1 `_ = (rr,ss)` >>
  `(case rr of INR ex => (INR ex,ss)
     | INL v => if v = BoolV T then (INL (),ss)
                else if v = BoolV F then (INR (AssertException str),ss)
                else (INR (Error (TypeError "not BoolV")),ss)) = (res,es')` by
    (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
     rewrite_tac[eval_assert_lit_bind] >>
     simp_tac std_ss [Once bind_def] >> asm_rewrite_tac[] >>
     Cases_on `rr` >> simp_tac (srw_ss()) [] >>
     rpt IF_CASES_TAC >> simp_tac (srw_ss()) [return_def, raise_def]) >>
  `!exc. rr = INR exc ==> no_control_exc exc` by
    (rpt strip_tac >> gvs[] >>
     qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `eval_expr cx e es` >>
     rename1 `_ = (raw,est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
     metis_tac[read_result_no_control, cj 1 eval_expr_no_control]) >>
  qexistsl_tac [`rr`, `ss`] >> asm_rewrite_tac[] >>
  Cases_on `rr` >> gvs[expr_res_ok_def, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[stmt_res_ok_def, no_control_exc_def] >> metis_tac[]
QED

Theorem assert_lit_expr_admissible:
  gas_admissible
    (eval_stmt cx
       (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str)))))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> pure_rewrite_tac[gas_admissible_def] >> rpt gen_tac >>
  disch_tac >>
  Cases_on `eval_stmt cx
    (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str))))
    (es with gas_obs := gs)` >>
  drule_all gas_admissible_result >> strip_tac >>
  drule_at (Pat `eval_stmt _ _ _ = _`) eval_assert_lit_forced_ok >>
  disch_then drule >> strip_tac >> gvs[]
QED

Theorem assert_lit_expr_exempt:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind
       (eval_stmt cx
          (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str)))))
       (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >> asm_simp_tac (srw_ss()) [eval_assert_lit_bind] >>
  pure_rewrite_tac[ignore_bind_def] >>
  once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem compile_assert_lit_parts:
  stmt_env cenv lctx ty
    (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str)))) sa =
    (cenv',sb) ==>
  ?op s1 ok s2 fl s3 s4 s5 buf sm s6.
    cenv' = cenv /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
    fresh_label "assert_ok" s1 = (ok,s2) /\
    fresh_label "assert_fail" s2 = (fl,s3) /\
    emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
    new_block fl s4 = (s4.cs_current_bb,s5) /\
    compile_bytelike_literal (MAP (n2w o ORD) str) ml s5 = (buf,sm) /\
    compile_revert_with_reason cenv
      (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf))
      (BaseT (StringT ml)) (32 + ((ml + 31) DIV 32) * 32) sm = ((),s6) /\
    new_block ok s6 = (s6.cs_current_bb,sb)
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       compile_reason_message_def, expr_type_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  Cases_on `lower_value compile_expr cenv (BaseT BoolT) e sa` >>
  rename1 `_ = (op,s1)` >> simp[] >>
  Cases_on `fresh_label "assert_ok" s1` >> rename1 `_ = (ok,s2)` >> simp[] >>
  Cases_on `fresh_label "assert_fail" s2` >> rename1 `_ = (fl,s3)` >> simp[] >>
  Cases_on `emit_inst JNZ [op; Label ok; Label fl] [] s3` >>
  rename1 `_ = (u,s4)` >> simp[] >>
  Cases_on `new_block fl s4` >> rename1 `_ = (v,s5)` >> simp[] >>
  Cases_on `compile_bytelike_literal (MAP (n2w o ORD) str) ml s5` >>
  rename1 `_ = (buf,sm)` >> simp[] >>
  qmatch_goalsub_abbrev_tac `compile_revert_with_reason cenv VV MT MS sm` >>
  Cases_on `compile_revert_with_reason cenv VV MT MS sm` >>
  rename1 `_ = (u6,s6)` >> simp[] >>
  Cases_on `new_block ok s6` >> rename1 `_ = (x7,s7)` >>
  simp[] >> strip_tac >>
  gvs[Abbr `VV`, Abbr `MT`, Abbr `MS`, type_memory_bytes_def] >>
  imp_res_tac new_block_props >> gvs[]
QED

(* The literal's buffer and the encoder stay in the block they start in. *)
Theorem lit_revert_extends:
  !bs ml sa buf sm cenv n mt M sb.
    compile_bytelike_literal bs ml sa = (buf, sm) /\
    compile_revert_with_reason cenv
      (LocatedValue (BaseT (StringT n)) (base_ptr buf)) mt M sm = ((), sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  drule bytelike_literal_shape >> strip_tac >>
  drule compile_revert_reason_shape >>
  disch_then (qx_choosel_then [`op`, `sn`] strip_assume_tac) >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, base_ptr_def, is_word_type_def, comp_return_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  simp[cs_extends_def, IS_PREFIX_APPEND]
QED

Theorem assert_lit_compiler_code:
  cs_extends sa s1 /\
  fresh_label "assert_ok" s1 = (ok,s2) /\
  fresh_label "assert_fail" s2 = (fl,s3) /\
  emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
  new_block fl s4 = (x5,s5) /\
  cs_extends s5 s6 /\
  new_block ok s6 = (x7,s7) /\ fn_has_code sa s7 func ==>
  cs_extends s1 s2 /\ cs_extends s2 s3 /\ cs_extends s3 s4 /\
  cs_extends s4 s5 /\ cs_extends s5 s6 /\ cs_extends s6 s7 /\
  fn_has_code sa s1 func /\ fn_has_code s3 s4 func /\
  fn_has_code s5 s6 func /\
  s3.cs_current_bb = s1.cs_current_bb /\
  s3.cs_current_insts = s1.cs_current_insts /\
  s5.cs_current_bb = fl /\ s5.cs_current_insts = [] /\
  s7.cs_current_bb = ok /\ s7.cs_current_insts = []
Proof
  strip_tac >>
  imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
  `cs_extends s1 s2 /\ cs_extends s2 s3 /\ cs_extends s3 s4 /\
   cs_extends s4 s5 /\ cs_extends s6 s7` by
    metis_tac[cs_extends_fresh_label, cs_extends_new_block,
              cs_appends_emit_helpers, cs_appends_def] >>
  simp[] >>
  metis_tac[fn_has_code_split, fn_has_code_mid, cs_extends_trans,
            cs_extends_refl]
QED

Theorem compile_assert_reason_lit_frag_mem:
  !d ctx func cx lctx RetQ cenv ty e ml str es.
    expr_type e = BaseT BoolT /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) /\
    LENGTH str <= ml /\
    type_memory_bytes cenv (BaseT (StringT ml)) < 2 ** 64 ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str)))))
      (eval_stmt cx
         (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str)))))
      es
Proof
  rpt gen_tac >> strip_tac >>
  `32 + ((ml + 31) DIV 32) * 32 < 2 ** 64` by
    (qpat_x_assum `type_memory_bytes _ _ < _` mp_tac >>
     simp[type_memory_bytes_def]) >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `stmt_env _ _ _ _ _ = _`) compile_assert_lit_parts >>
  strip_tac >> gvs[] >>
  `cs_extends sa s1` by metis_tac[] >>
  drule_all lit_revert_extends >> strip_tac >>
  drule_all assert_lit_compiler_code >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >>
     imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
     imp_res_tac emit_inst_extends >> gvs[] >> decide_tac) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[assert_lit_expr_admissible] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then drule >> simp[] >>
  disch_then (qspec_then `s0` mp_tac) >> simp[] >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `?res es_end r. _` strip_assume_tac >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  qexists_tac `marks` >> disj2_tac >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule assert_lit_expr_exempt >> simp[]
QED

Resume compile_assert_reason_lit_frag_mem[normal]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
  `~t.vs_halted` by metis_tac[gas_path_mem_exec, gas_path_normal] >>
  `?b. v = BoolV b` by
    (Cases_on `eval_stmt cx
       (Assert e (AssertReason (Literal (BaseT (StringT ml)) (StringL str))))
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` >>
     drule_all gas_admissible_result >> strip_tac >>
     drule_at (Pat `eval_stmt _ _ _ = _`) eval_assert_lit_forced_ok >>
     disch_then drule >> strip_tac >>
     qpat_x_assum `!tail. _ = _` (qspec_then `[]` assume_tac) >>
     gvs[bind_def]) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    gvs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
        typed_val_to_w256_def, val_to_w256_def] >>
  `gas_path_mem ctx func t 0
     (OK (jump_to (if b then sb.cs_current_bb else s5.cs_current_bb) t))` by
    (imp_res_tac emit_inst_extends >>
     irule assert_jnz_zero_path_mem >> simp[] >>
     qexistsl_tac [`op`, `s3`, `s4`] >> simp[]) >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!sa op sb. _` kall_tac >>
  Cases_on `b`
  >- suspend "true"
  >> suspend "false"
QED

Resume compile_assert_reason_lit_frag_mem[exception]:
  markerLib.RESUME_TAC >>
  Cases_on `res` >- fs[expr_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >>
  conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >> strip_tac >> simp[] >>
      gen_tac >> asm_simp_tac (srw_ss()) [eval_assert_lit_bind] >>
      simp[Once bind_def]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_assert_reason_lit_frag_mem[true]:
  markerLib.RESUME_TAC >>
  gvs[] >>
  qexistsl_tac [`INL ()`, `es_end`, `OK (jump_to sb.cs_current_bb t)`] >>
  conj_tac
  >- (conj_tac
      >- (rpt gen_tac >>
          asm_simp_tac (srw_ss()) [eval_assert_lit_bind] >>
          simp[Once bind_def, return_def]) >>
      metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]) >>
  disj1_tac >>
  drule_all assert_success_post_mem >> simp[]
QED

Resume compile_assert_reason_lit_frag_mem[false]:
  markerLib.RESUME_TAC >>
  gvs[] >>
  `?EE. stmt_state_rel ctx func cenv cx EE (jump_to s5.cs_current_bb t)` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     rewrite_tac[stmt_state_rel_jump_to] >> metis_tac[]) >>
  `?u. gas_path_mem ctx func (jump_to s5.cs_current_bb t) 0
         (Abort Revert_abort u)` by
    (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `EE`,
                  `jump_to s5.cs_current_bb t`, `str`, `ml`,
                  `BaseT (StringT ml)`, `s5`, `buf`, `sm`, `s6`] mp_tac
       lit_reason_revert_path_mem >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         simp[jump_to_def]) >>
     disch_then ACCEPT_TAC) >>
  qexistsl_tac [`INR (AssertException str)`, `es_end`,
                `Abort Revert_abort u`] >>
  conj_tac
  >- (conj_tac
      >- (gen_tac >> simp[eval_assert_lit_bind] >>
          simp[Once bind_def, raise_def]) >>
      metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]) >>
  disj2_tac >> simp[exit_result_def, stmt_exit_def, expr_exit_def]
QED

Finalise compile_assert_reason_lit_frag_mem
