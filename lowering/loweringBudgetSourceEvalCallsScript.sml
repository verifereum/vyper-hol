Theory loweringBudgetSourceEvalCalls
Ancestors
  pair list rich_list vyperAST vyperState vyperInterpreter vyperContext
  vyperMisc vyperValue vyperCallOutcome vyperCallOutcomeProps vyperCall
  supportedExprTraverse supportedStmtTraverse supportedDecls supportedProgram
  bodyStorageCases evalNoHalt vyperTypeCallGraph exprSimWordArgs
Libs
  pairLib monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val _ = overload_on ("bind", ``vyperState$bind``);
val _ = overload_on ("return", ``vyperState$return``);
val _ = overload_on ("ignore_bind", ``vyperState$ignore_bind``);
val _ = overload_on ("raise", ``vyperState$raise``);
val _ = overload_on ("try", ``vyperState$try``);
val _ = overload_on ("finally", ``vyperState$finally``);

Theorem bind_exception[local]:
  bind f g s = (INR exc,s') <=>
  f s = (INR exc,s') \/ ?v t. f s = (INL v,t) /\ g v t = (INR exc,s')
Proof
  simp[bind_def] >> Cases_on `f s` >> Cases_on `q` >> simp[]
QED

Theorem exprs_pre_every[local]:
  !es. EVERY (\e. ~supported_expr_exists p e /\ EVERY Q (int_calls_expr e)) es
    <=> ~supported_exprs_exists p es /\ EVERY Q (int_calls_exprs es)
Proof
  Induct >> simp[supported_expr_exists_def, int_calls_expr_def] >> metis_tac[]
QED

val syn_ss = [supported_expr_exists_def, expr_evm_run_root_def,
  int_calls_expr_def, EVERY_APPEND, exprs_pre_every];
val case_ss = [bind_exception, ignore_bind_def, return_def, raise_def,
  type_check_def, check_def, assert_def, lift_option_type_def,
  lift_option_def, get_scopes_def, set_scopes_def, FORALL_PROD, EXISTS_PROD,
  COND_RATOR, get_accounts_def, get_transient_storage_def, update_accounts_def,
  update_transient_def, update_pending_deletions_def, append_logs_def,
  record_storage_backend_def, record_storage_event_def];

(* These are the literal evaluate_ind Call clauses. Only P1, P4, P5 and
   P10 occur in them; the lambdas match eval_no_halt_every's predicate order. *)
val (preds, ind_body) = strip_forall (concl evaluate_ind);
val clauses = strip_conj (fst (dest_imp ind_body));
fun call_clause tm =
  let val (_, c) = strip_imp (snd (strip_forall tm))
      val (_, args) = strip_comb c
  in length args = 2 andalso
     (fst (dest_const (fst (strip_comb (List.nth (args,1))))) = "Call"
      handle HOL_ERR _ => false)
  end;
val stmts_pred = ``\cx ss. ~supported_stmts_expr_exists expr_evm_run_root ss /\
  EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts ss) ==>
  !st st'. eval_stmts cx ss st =
    (INR (Error (RuntimeError "create outcome accounts")),st') ==> F``;
val expr_pred = ``\cx e. ~supported_expr_exists expr_evm_run_root e /\
  EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e) ==>
  !st st'. eval_expr cx e st =
    (INR (Error (RuntimeError "create outcome accounts")),st') ==> F``;
val exprs_pre = ``\cx e. ~supported_expr_exists expr_evm_run_root e /\
  EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e)``;
val exprs_pred = ``\cx es. EVERY (^exprs_pre cx) es ==>
  !st st'. eval_exprs cx es st =
    (INR (Error (RuntimeError "create outcome accounts")),st') ==> F``;
val results_pred = ``\cx es. EVERY (^exprs_pre cx) es ==>
  !st st'. eval_expr_results cx es st =
    (INR (Error (RuntimeError "create outcome accounts")),st') ==> F``;
val call_cases = list_mk_conj (map
  (subst [List.nth(preds,1) |-> stmts_pred,
          List.nth(preds,4) |-> expr_pred,
          List.nth(preds,5) |-> exprs_pred,
          List.nth(preds,10) |-> results_pred])
  (filter call_clause clauses));

Theorem source_no_create_error_call_cases:
  ^call_cases
Proof
  BETA_TAC >> rpt conj_tac >> rpt gen_tac
  >~ [`Call _ (IntCall _) _ _`] >- suspend "IntCall"
  >~ [`Call _ (ExtCall _ _ _ _) _ _`] >- suspend "ExtCall"
  >~ [`Call _ (Send _) _ _`] >- suspend "Send"
  >~ [`Call _ (RawCallTarget _) _ _`] >- suspend "RawCall"
  >~ [`Call _ (RawCallCalldataTarget _) _ _`] >- suspend "RawCalldata"
  >~ [`Call _ RawLog _ _`] >- suspend "RawLog"
  >~ [`Call _ RawRevert _ _`] >- suspend "RawRevert"
  >> simp[supported_expr_exists_def, expr_evm_run_root_def]
QED

Resume source_no_create_error_call_cases[Send]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp([Once evaluate_def] @ case_ss) >> gvs(syn_ss @ case_ss) >>
  rpt strip_tac >>
  rename1 `eval_send cx has_gas vs t = _` >>
  Cases_on `vs` >- gvs[eval_send_def, raise_def] >>
  rename1 `h::rest` >> Cases_on `rest` >- gvs[eval_send_def, raise_def] >>
  gvs([eval_send_def, AllCaseEqs(), option_CASE_rator,
       frame_call_value_def, check_not_static_def,
       adopt_call_outcome_equation] @ case_ss) >>
  gvs([AllCaseEqs()] @ case_ss) >>
  imp_res_tac take_call_outcome_error >> gvs[]
QED

Resume source_no_create_error_call_cases[IntCall]:
  strip_tac >> simp syn_ss >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  Cases_on `MEM (NONE,fn) cx.stk`
  >- (rpt (qpat_x_assum `!x. _` kall_tac) >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp([Once evaluate_def] @ case_ss)) >>
  Cases_on `lookup_callable_function cx.in_deploy fn tops`
  >- (rpt (qpat_x_assum `!x. _` kall_tac) >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp([Once evaluate_def] @ case_ss)) >>
  rename1 `_ = SOME tup` >> PairCases_on `tup` >>
  drule_all supported_callable_storage_syntax >> strip_tac >> gvs[] >>
  Cases_on `LENGTH es = LENGTH tup2`
  >- (gvs(syn_ss @ case_ss @ [eval_exprs_nil, finally_def, bind_def,
                              push_function_def]) >>
      drule_all eval_expr_intcall_empty_defaults >>
      disch_then (fn th => qpat_x_assum `eval_expr _ _ _ = _`
        (mp_tac o REWRITE_RULE [th])) >>
      simp(case_ss @ [push_function_def]) >>
      rpt gen_tac >> strip_tac >>
      Cases_on `bind_arguments (get_tenv cx) tup2 vs` >>
      simp[return_def, raise_def] >> strip_tac >>
      Cases_on `evaluate_type (get_tenv cx) tup4` >>
      simp[return_def, raise_def] >>
      conj_tac >- (Cases_on `tup1` >>
        Cases_on `cx.nonreentrant_slot` >>
        simp([acquire_nonreentrant_lock_def, check_not_static_def,
              bind_def] @ tl case_ss) >> rpt (IF_CASES_TAC >> simp[])) >>
      rpt gen_tac >> strip_tac >>
      reverse conj_tac >- (rpt gen_tac >> strip_tac >>
        Cases_on `safe_cast x' rv` >> simp[return_def, raise_def]) >>
      strip_tac >>
      qpat_x_assum `!s0 vs t0 s1 env t1 s2 rtv t2 s3 t3. _`
        (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
      simp[return_def, raise_def] >>
      goal_assum (drule_at Any) >>
      simp[LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM] >>
      conj_tac >- (gvs[EVERY_MEM, get_module_code_def] >> metis_tac[]) >>
      qmatch_asmsub_abbrev_tac `finally_unless_halt _ _ initial = _` >>
      Cases_on `eval_stmts (cx with stk updated_by CONS (NONE,fn)) tup5 initial` >>
      rename1 `_ = (body_res,body_st)` >> Cases_on `body_res` >>
      qpat_x_assum `finally_unless_halt _ _ _ = _` mp_tac >>
      simp([finally_unless_halt_def, finally_def, pop_function_def,
            try_def, bind_def, release_nonreentrant_lock_def] @ tl case_ss) >>
      Cases_on `cx.nonreentrant_slot` >>
      simp([COND_RATOR, bind_def] @ tl case_ss) >>
      rpt (IF_CASES_TAC >> simp[]) >>
      rename1 `eval_stmts _ _ initial = (INR exc,body_st)` >>
      Cases_on `exc` >> simp[handle_function_def, return_def, raise_def] >>
      Cases_on `tup1 /\ tup0 <> View /\ tup0 <> Pure` >>
      simp[return_def, raise_def, bind_def] >> rpt strip_tac >> gvs[] >> qexistsl [`initial`, `body_st`] >> simp[]) >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp([Once evaluate_def] @ case_ss) >>
  Cases_on `LENGTH es < LENGTH tup2` >- simp[] >>
  disj1_tac >> decide_tac
QED
Resume source_no_create_error_call_cases[ExtCall]:
  rpt strip_tac >> pop_assum mp_tac >> gvs syn_ss >>
  `EVERY (^exprs_pre cx) es` by gvs[exprs_pre_every] >>
  `!n. EVERY (^exprs_pre cx) (TAKE n es) /\
       EVERY (^exprs_pre cx) (DROP n es) /\
       EVERY (^exprs_pre cx) (TAKE n (DROP 1 es))` by
    metis_tac[EVERY_TAKE, EVERY_DROP] >>
  simp([Once evaluate_def] @ case_ss) >> gvs(syn_ss @ case_ss) >>
  rpt strip_tac >> gvs[]
  >- metis_tac[] >- metis_tac[] >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  qmatch_asmsub_abbrev_tac `eval_ext_call cx is_static' skip_check sig opts operands s` >>
  PairCases_on `sig` >> Cases_on `operands` >- gvs[eval_ext_call_def, raise_def] >>
  gvs([eval_ext_call_def, frame_call_value_def,
       AllCaseEqs(), option_CASE_rator] @ case_ss) >>
  gvs([eval_ext_call_effects_def, AllCaseEqs(),
       option_CASE_rator, adopt_call_outcome_equation] @ case_ss) >>
  imp_res_tac take_call_outcome_error >> gvs[] >>
  gvs[vyperStateTheory.lift_sum_runtime_def,
      vyperABITheory.evaluate_abi_decode_return_def,
      vyperABITheory.evaluate_abi_decode_returndata_def,
      vyperABITheory.decode_abi_value_def, AllCaseEqs(),
      raise_def, return_def] >>
  gvs[COND_RATOR, option_CASE_rator, sum_CASE_rator,
      AllCaseEqs(), raise_def, return_def]
QED
Resume source_no_create_error_call_cases[RawCall]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp([Once evaluate_def] @ case_ss) >> gvs(syn_ss @ case_ss) >>
  rpt strip_tac >> gvs([AllCaseEqs()] @ case_ss) >>
  gvs([option_CASE_rator, AllCaseEqs()] @ case_ss) >>
  gvs([eval_raw_call_def, frame_call_value_def, adopt_call_outcome_equation,
       option_CASE_rator, AllCaseEqs()] @ case_ss) >>
  imp_res_tac take_call_outcome_error >> gvs[]
QED
Resume source_no_create_error_call_cases[RawCalldata]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp([Once evaluate_def] @ case_ss) >> gvs(syn_ss @ case_ss) >>
  rpt strip_tac >> gvs([AllCaseEqs(), option_CASE_rator] @ case_ss) >>
  gvs([eval_raw_call_def, frame_call_value_def, adopt_call_outcome_equation,
       option_CASE_rator, AllCaseEqs()] @ case_ss) >>
  imp_res_tac take_call_outcome_error >> gvs[]
QED
Resume source_no_create_error_call_cases[RawLog]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp([Once evaluate_def] @ case_ss) >> gvs(syn_ss @ case_ss) >>
  rpt strip_tac >> gvs([AllCaseEqs(), option_CASE_rator,
      check_not_static_def] @ case_ss)
QED
Resume source_no_create_error_call_cases[RawRevert]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp([Once evaluate_def] @ case_ss) >> gvs(syn_ss @ case_ss) >>
  rpt strip_tac >> gvs([AllCaseEqs(), option_CASE_rator] @ case_ss)
QED
Finalise source_no_create_error_call_cases
