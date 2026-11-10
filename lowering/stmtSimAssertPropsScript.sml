(* Actual source-action boundaries for assertions. *)
Theory stmtSimAssertProps
Ancestors
  stmtSimIfProps stmtSimDefs exprSimDefs vyperInterpreter vyperState
  gasContext gasExemptCert stmtSimProps fragGasPath gasCount
  bodyMemoryDefs allocaHistory
  emitHelperProps compileEnv venomExecSemantics venomExecProofs venomInst
  venomState fragExec loweringPosts stmtLowering exprLowering emitHelper exprLoweringProps
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

Theorem assert_success_post:
  expr_post ctx func cenv cx e es sa s1 s0 ee (BoolV T) op t /\
  ~t.vs_halted /\ sb.cs_current_insts = [] ==>
  stmt_post ctx func cx lctx cenv cenv sa sb s0 (INL ()) ee
    (jump_to sb.cs_current_bb t)
Proof
  strip_tac >> gvs[expr_post_def, stmt_post_def] >>
  simp[stmt_lands_def, stmt_state_rel_jump_to, block_is_terminated_def,
       cenv_top_ext_refl] >>
  gvs[jump_to_def, lookup_var_def]
QED

Theorem assert_success_post_mem:
  expr_post ctx func cenv cx e es sa s1 s0 ee (BoolV T) op t /\
  ~t.vs_halted /\ sb.cs_current_insts = [] /\
  sa.cs_next_var <= sb.cs_next_var /\
  return_buf_frame d cenv sa s0 /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next ==>
  ?cenv''. stmt_lands lctx sb (INL () : unit + exception)
      (jump_to sb.cs_current_bb t) /\
    ~(jump_to sb.cs_current_bb t).vs_halted /\
    (~block_is_terminated sb /\ cenv'' = cenv) /\
    cenv_top_ext cenv cenv'' ee.scopes /\
    stmt_state_rel ctx func cenv'' cx ee (jump_to sb.cs_current_bb t) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x (jump_to sb.cs_current_bb t) = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP (jump_to sb.cs_current_bb t).vs_allocas aid = SOME b) /\
    return_buf_frame d cenv'' sb (jump_to sb.cs_current_bb t) /\
    alloca_history func (jump_to sb.cs_current_bb t) /\
    s0.vs_alloca_next <= (jump_to sb.cs_current_bb t).vs_alloca_next
Proof
  strip_tac >>
  drule_all assert_success_post >>
  simp[stmt_post_def] >> strip_tac >>
  conj_tac
  >- (simp[return_buf_frame_jump_to] >> irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `s0`, `sa`] >>
      gvs[expr_post_def]) >>
  gvs[alloca_history_def, jump_to_def]
QED
