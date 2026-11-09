(* Source-domain checks for the prepared raw_call boundary.  Runtime errors
   remain admissible: source typing does not validate oracle accounts. *)
Theory rawCallSourceDomainPtr
Ancestors
  rawCallSourceActionPtr rawCallShapePtr exprSimDefs gasContext
  exprLoweringProps compileEnv vyperInterpreter vyperState vyperCallOutcome
  vyperCallOutcomeProps exprSimSend vyperTypeExtCallCore

Theorem raw_call_prepared_source_domain:
  stmt_state_rel ctx func cenv cx es s ==>
  ~cx.txn.is_static /\ IS_SOME es.outcomes /\
  frame_call_value cx (if stat then NONE else SOME amount) es =
    (INL (if stat then NONE else SOME amount),es) /\
  (stat = IS_NONE (if stat then NONE else SOME amount))
Proof
  strip_tac >>
  `~cx.txn.is_static /\ es.outcomes = SOME s.vs_outcomes` by
    fs[stmt_state_rel_def, state_rel_def] >>
  simp[vyperInterpreterTheory.frame_call_value_def, vyperStateTheory.return_def] >>
  Cases_on `stat` >> simp[]
QED

Theorem raw_call_prepared_take_error:
  stmt_state_rel ctx func cenv cx es s /\
  take_call_outcome target data value_opt es = (INR exc,ee) ==>
  exc = Error (RuntimeError "call outcome accounts")
Proof
  strip_tac >>
  `es.outcomes = SOME s.vs_outcomes` by fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `take_call_outcome _ _ _ _ = _` mp_tac >>
  simp[vyperCallOutcomeTheory.take_call_outcome_def] >>
  pairarg_tac >> rw[] >> gvs[AllCaseEqs()]
QED

Theorem raw_call_runtime_failure_admissible:
  expr_vv_res_ok (INR (Error (RuntimeError msg))) /\
  expr_res_ok (INR (Error (RuntimeError msg))) /\
  expr_exit (INR (Error (RuntimeError msg))) (Abort reason s)
Proof
  simp[expr_vv_res_ok_def, expr_res_ok_def, expr_exit_def]
QED

Theorem raw_call_bad_flags:
  ~(~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
    ((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0)) ==>
  eval_raw_call cx flags target data amount gas es =
    (INR (Error (TypeError "raw_call flags/value")),es)
Proof
  strip_tac >> fs[vyperInterpreterTheory.eval_raw_call_def, vyperStateTheory.type_check_def,
    vyperStateTheory.assert_def, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.bind_def, vyperStateTheory.raise_def]
QED

Theorem raw_call_admissible_flags:
  gas_admissible (eval_raw_call cx flags target data amount gas) expr_vv_res_ok es ==>
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  ((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0)
Proof
  strip_tac >> spose_not_then assume_tac >>
  `eval_raw_call cx flags target data amount gas (es with gas_obs := []) =
    (INR (Error (TypeError "raw_call flags/value")),es with gas_obs := [])` by
    (irule raw_call_bad_flags >> metis_tac[]) >>
  drule_all gas_admissible_result >> simp[expr_vv_res_ok_def]
QED

Theorem raw_call_prepared_take_success:
  stmt_state_rel ctx func cenv cx es s /\ expr_sim_inv cenv cx env es ==>
  ?rq outcome ee. take_call_outcome target data value_opt es = (INL (rq,outcome),ee)
Proof
  strip_tac >>
  `outcomes_accounts_typed es.outcomes /\ accounts_runtime_well_typed es.accounts` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def,
      accounts_runtime_well_typed_accounts_well_typed] >>
  Cases_on `take_call_outcome target data value_opt es` >>
  rename1 `take_call_outcome _ _ _ _ = (res,ee)` >>
  Cases_on `res`
  >- (PairCases_on `x` >> metis_tac[]) >>
  drule_all raw_call_prepared_take_error >> strip_tac >> gvs[] >>
  drule_all take_call_outcome_typed >> simp[] >> metis_tac[pairTheory.FST]
QED
