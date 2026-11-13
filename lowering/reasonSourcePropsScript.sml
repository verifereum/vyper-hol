(* Shared source-semantic boundaries for reason-bearing exits. *)
Theory reasonSourceProps
Ancestors
  stmtSimDefs stmtSimProps stmtSimIfProps exprSimDefs exprSimProps exprSimMemorySource
  loweringPosts gasSummary gasExemptCert gasSummaryCompose gasContext
  vyperInterpreter vyperState vyperValue vyperValueOperation
  vyperExprNoControl vyperStatePreservation list rich_list
Libs
  monadsyntax

Theorem eval_assert_reason_bind:
  eval_stmt cx (Assert e (AssertReason r)) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. if v = BoolV T then return ()
           else if v = BoolV F then eval_stmt cx (Raise (RaiseReason r))
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

Theorem assert_reason_expr_admissible:
  gas_admissible (eval_stmt cx (Assert e (AssertReason r)))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> pure_rewrite_tac[gas_admissible_def] >>
  rpt gen_tac >> disch_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `_ = (INR ex,ee)` >>
  `no_control_exc ex` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
     rename1 `_ = (raw,st)` >> Cases_on `raw` >> simp[] >>
     metis_tac[read_result_no_control, cj 1 eval_expr_no_control]) >>
  `eval_stmt cx (Assert e (AssertReason r)) (es with gas_obs := gs) =
    (INR ex,ee)` by simp[eval_assert_reason_bind, bind_def] >>
  drule_all gas_admissible_result >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

Theorem assert_reason_raise_admissible:
  gas_admissible (eval_stmt cx (Assert e (AssertReason r)))
    (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV F),mid with gas_obs := tail)) ==>
  gas_admissible (eval_stmt cx (Raise (RaiseReason r)))
    (stmt_res_ok lctx) (mid with gas_obs := [])
Proof
  strip_tac >> simp[gas_admissible_def] >> rpt strip_tac >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `xs ++ gs` mp_tac) >>
  simp[eval_assert_reason_bind, bind_def] >> metis_tac[]
QED

Theorem eval_raise_reason_non_normal:
  eval_stmt cx (Raise (RaiseReason r)) es = (res,ee) ==>
  res <> INL () /\ res <> INR BreakException /\ res <> INR ContinueException
Proof
  simp[Once evaluate_def, bind_def, lift_option_type_def,
       lift_option_def, raise_def, return_def] >>
  Cases_on `eval_expr cx r es` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw`
  >- (simp[] >> rename1 `read_result cx v st` >>
      Cases_on `read_result cx v st` >> rename1 `_ = (forced,sf)` >>
      Cases_on `forced`
      >- (simp[] >> rename1 `dest_StringV sv` >> Cases_on `dest_StringV sv` >>
          simp[raise_def, return_def] >> rpt strip_tac >> gvs[]) >>
      simp[] >> strip_tac >> gvs[] >>
      drule read_result_no_control >> simp[no_control_exc_def] >>
      rpt strip_tac >> gvs[]) >>
  simp[] >> strip_tac >> gvs[] >>
  drule (cj 1 eval_expr_no_control) >> simp[no_control_exc_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem assert_reason_expr_exempt:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (Assert e (AssertReason r))) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >> pure_rewrite_tac[eval_assert_reason_bind, ignore_bind_def] >>
  once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem eval_raise_reason_bind:
  eval_stmt cx (Raise (RaiseReason r)) =
  bind (eval_expr cx r)
    (\tv. do v <- read_result cx tv;
             str <- lift_option_type (dest_StringV v) "not StringV";
             raise (AssertException str) od)
Proof
  simp[FUN_EQ_THM, Once evaluate_def, bind_def] >> gen_tac >>
  Cases_on `eval_expr cx r x` >> rename1 `_ = (raw, ee)` >>
  Cases_on `raw` >> simp[bind_def]
QED

Theorem raise_reason_raw_exempt:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_expr cx r) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (Raise (RaiseReason r))) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate)
Proof
  strip_tac >> rewrite_tac[eval_raise_reason_bind] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[]
QED

Theorem eval_raise_reason_forced_bind:
  eval_stmt cx (Raise (RaiseReason r)) =
  bind (bind (eval_expr cx r) (read_result cx))
    (\v. do str <- lift_option_type (dest_StringV v) "not StringV";
            raise (AssertException str) od)
Proof
  simp[eval_raise_reason_bind, bind_assoc]
QED

Theorem raise_reason_forced_admissible:
  gas_admissible (eval_stmt cx (Raise (RaiseReason r)))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx r) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> pure_rewrite_tac[gas_admissible_def] >>
  rpt gen_tac >> disch_tac >> Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `_ = (INR ex,ee)` >>
  `no_control_exc ex` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def] >>
     Cases_on `eval_expr cx r (es with gas_obs := gs)` >>
     rename1 `_ = (raw,st)` >> Cases_on `raw` >> simp[] >>
     metis_tac[read_result_no_control, cj 1 eval_expr_no_control]) >>
  `eval_stmt cx (Raise (RaiseReason r)) (es with gas_obs := gs) = (INR ex,ee)` by
    simp[eval_raise_reason_forced_bind, bind_def] >>
  drule_all gas_admissible_result >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

Theorem raise_reason_raw_admissible:
  gas_admissible (eval_stmt cx (Raise (RaiseReason r)))
    (stmt_res_ok lctx) es ==>
  gas_admissible (eval_expr cx r) expr_vv_res_ok es
Proof
  strip_tac >> irule forced_expr_admissible_raw >>
  drule raise_reason_forced_admissible >> simp[]
QED

Theorem eval_raise_string_literal_reason:
  eval_stmt cx (Raise (RaiseReason (Literal ann (StringL str)))) es =
    (INR (AssertException str),es)
Proof
  simp[eval_raise_reason_bind, Once evaluate_def, evaluate_literal_def,
       bind_def, return_def, read_result_def, lift_option_type_def,
       dest_StringV_def, raise_def]
QED
