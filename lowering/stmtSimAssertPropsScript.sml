(* Actual source-action boundaries for assertions. *)
Theory stmtSimAssertProps
Ancestors
  stmtSimIfProps stmtSimDefs exprSimDefs vyperInterpreter vyperState
  gasContext gasExemptCert
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
