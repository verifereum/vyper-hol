(* Actual source-action boundaries for assertions. *)
Theory stmtSimAssertProps
Ancestors
  stmtSimIfProps stmtSimDefs exprSimDefs vyperInterpreter vyperState
  gasContext gasExemptCert stmtSimProps fragGasPath gasCount
  emitHelperProps compileEnv venomExecSemantics venomExecProofs venomInst
  venomState fragExec loweringPosts stmtLowering exprLowering emitHelper
Libs
  monadsyntax

Theorem eval_assert_bind:
  (ak = AssertBare \/ ak = AssertUnreachable) ==>
  eval_stmt cx (Assert e ak) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. if v = BoolV T then return ()
           else if v = BoolV F then
             raise (AssertException (if ak = AssertBare then "" else "UNREACHABLE"))
           else raise (Error (TypeError "not BoolV")))
Proof
  strip_tac >> gvs[] >> simp[FUN_EQ_THM, Once evaluate_def,
    eval_expr_switch_forced] >> gen_tac >>
  simp[bind_def] >>
  Cases_on `eval_expr cx e x` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `read_result cx v st` >>
  Cases_on `read_result cx v st` >> rename1 `_ = (forced,sf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem assert_expr_admissible:
  (ak = AssertBare \/ ak = AssertUnreachable) /\
  gas_admissible (eval_stmt cx (Assert e ak)) (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> pure_rewrite_tac[gas_admissible_def] >> rpt gen_tac >>
  disch_tac >>
  Cases_on `eval_stmt cx (Assert e ak) (es with gas_obs := gs)` >>
  drule_all gas_admissible_result >> strip_tac >>
  drule_at (Pat `eval_stmt _ _ _ = _`) eval_assert_forced_ok >>
  disch_then (qspec_then `lctx` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[bind_def]
QED

Theorem assert_expr_exempt:
  (ak = AssertBare \/ ak = AssertUnreachable) /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (Assert e ak)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >> asm_simp_tac (srw_ss()) [eval_assert_bind] >>
  pure_rewrite_tac[ignore_bind_def] >>
  once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem assert_jnz_zero_path:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []] /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand op s = SOME (if b then 1w else 0w) ==>
  gas_path ctx func s 0 (OK (jump_to (if b then lt else lf) s))
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule step_jnz_behavior >>
  disch_then (qspecl_then [`lt`, `lf`, `sa.cs_next_id`] assume_tac) >>
  `gas_path_edge ctx func s 0 (OK (jump_to (if b then lt else lf) s))` by
    (rewrite_tac[gas_path_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jnz_behavior, is_terminator_def] >>
     Cases_on `b` >> gvs[] >> metis_tac[]) >>
  `~(jump_to (if b then lt else lf) s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem compile_assert_parts:
  (ak = AssertBare \/ ak = AssertUnreachable) /\
  stmt_env cenv lctx ty (Assert e ak) sa = (cenv',sb) ==>
  ?op s1 ok s2 fl s3 s4 s5 s6.
    cenv' = cenv /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
    fresh_label "assert_ok" s1 = (ok,s2) /\
    fresh_label "assert_fail" s2 = (fl,s3) /\
    emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
    new_block fl s4 = (s4.cs_current_bb,s5) /\
    emit_inst (if ak = AssertBare then REVERT else INVALID)
      (if ak = AssertBare then [Lit 0w; Lit 0w] else []) [] s5 = ((),s6) /\
    new_block ok s6 = (s6.cs_current_bb,sb)
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr cenv (BaseT BoolT) e sa` >>
  rename1 `_ = (op,s1)` >> simp[] >>
  Cases_on `fresh_label "assert_ok" s1` >> rename1 `_ = (ok,s2)` >> simp[] >>
  Cases_on `fresh_label "assert_fail" s2` >> rename1 `_ = (fl,s3)` >> simp[] >>
  Cases_on `emit_inst JNZ [op; Label ok; Label fl] [] s3` >>
  rename1 `_ = (u,s4)` >> simp[] >>
  Cases_on `new_block fl s4` >> rename1 `_ = (v,s5)` >> simp[] >>
  qmatch_goalsub_abbrev_tac `emit_inst opc ops [] s5` >>
  Cases_on `emit_inst opc ops [] s5` >> rename1 `_ = (u6,s6)` >>
  simp[] >> Cases_on `new_block ok s6` >> rename1 `_ = (x7,s7)` >>
  simp[] >> strip_tac >> gvs[] >>
  imp_res_tac new_block_props >> gvs[]
QED

Theorem assert_compiler_code:
  cs_extends sa s1 /\
  fresh_label "assert_ok" s1 = (ok,s2) /\
  fresh_label "assert_fail" s2 = (fl,s3) /\
  emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
  new_block fl s4 = (x5,s5) /\
  emit_inst opc ops [] s5 = ((),s6) /\
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
   cs_extends s4 s5 /\ cs_extends s5 s6 /\ cs_extends s6 s7` by
    metis_tac[cs_extends_fresh_label, cs_extends_new_block,
              cs_appends_emit_helpers, cs_appends_def] >>
  simp[] >>
  metis_tac[fn_has_code_split, fn_has_code_mid, cs_extends_trans,
            cs_extends_refl]
QED
