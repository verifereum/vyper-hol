(* Source-domain checks for the prepared raw_call boundary.  Runtime errors
   remain admissible: source typing does not validate oracle accounts. *)
Theory rawCallSourceDomainPtr
Ancestors
  rawCallSourceActionPtr rawCallShapePtr exprSimDefs gasContext
  exprLoweringProps compileEnv loweringStateRelDefs vyperInterpreter vyperState vyperCallOutcome
  vyperCallOutcomeProps exprSimSend vyperTypeExtCallCore

Theorem raw_call_prepared_source_domain:
  stmt_state_rel H ctx func cenv cx es s ==>
  IS_SOME es.outcomes /\
  frame_call_value cx (if stat then NONE else SOME amount) es =
    (if cx.txn.is_static /\ ~stat /\ amount <> 0 then
       INR (Error (RuntimeError "write in static context"))
     else INL (if stat \/ cx.txn.is_static then NONE else SOME amount),es) /\
  ((stat \/ cx.txn.is_static) =
    IS_NONE (if stat \/ cx.txn.is_static then NONE else SOME amount))
Proof
  strip_tac >>
  `es.outcomes = SOME s.vs_outcomes` by
    fs[stmt_state_rel_def, state_rel_def] >>
  Cases_on `cx.txn.is_static` >> Cases_on `stat` >> Cases_on `amount = 0` >>
  simp[vyperInterpreterTheory.frame_call_value_def, vyperStateTheory.return_def,
    vyperStateTheory.check_def,vyperStateTheory.assert_def,
    vyperStateTheory.ignore_bind_def,vyperStateTheory.bind_def]
QED

Theorem raw_call_prepared_take_error:
  stmt_state_rel H ctx func cenv cx es s /\
  take_call_outcome target data value_opt es = (INR exc,ee) ==>
  exc = Error (RuntimeError "call outcome accounts")
Proof
  strip_tac >>
  `es.outcomes = SOME s.vs_outcomes` by fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `take_call_outcome _ _ _ _ = _` mp_tac >>
  simp[vyperCallOutcomeTheory.take_call_outcome_def,
    vyperCallOutcomeTheory.take_request_outcome_def] >>
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
  stmt_state_rel H ctx func cenv cx es s /\ expr_sim_inv cenv cx env es ==>
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

Theorem raw_call_prepared_source_total:
  stmt_state_rel H ctx func cenv cx es s /\ expr_sim_inv cenv cx env es /\
  ~flags.rcf_is_delegate /\
  gas_admissible (eval_raw_call cx flags target data amount gas) expr_vv_res_ok es ==>
  if cx.txn.is_static /\ amount <> 0 then
    (!tail. eval_raw_call cx flags target data amount gas (es with gas_obs := tail) =
      (INR (Error (RuntimeError "write in static context")),es with gas_obs := tail))
  else
    ?rq outcome es1.
      take_call_outcome target data
        (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount) es =
        (INL (rq,outcome),es1) /\
      (!tail. eval_raw_call cx flags target data amount gas (es with gas_obs := tail) =
        (if flags.rcf_revert_on_failure /\ ~outcome.co_success then
           INR (Error (RevertData outcome.co_returnData))
         else INL (Value (if flags.rcf_revert_on_failure then
           if flags.rcf_max_outsize = 0 then NoneV
           else BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)
         else if flags.rcf_max_outsize = 0 then BoolV outcome.co_success
         else ArrayV (TupleV [BoolV outcome.co_success;
           BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)]))),
         SND (adopt_call_outcome rq outcome es1) with gas_obs := tail))
Proof
  strip_tac >> drule raw_call_admissible_flags >> strip_tac >>
  `flags.rcf_is_static ==> amount = 0` by metis_tac[] >>
  Cases_on `cx.txn.is_static /\ amount <> 0`
  >- (asm_rewrite_tac[] >> gen_tac >> irule raw_call_static_value_abort >> fs[]) >>
  asm_rewrite_tac[] >>
  drule_all raw_call_prepared_take_success >>
  disch_then (qspecl_then [`if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount`,
    `target`, `data`] strip_assume_tac) >>
  qexistsl_tac [`rq`, `outcome`, `ee`] >> simp[] >> gen_tac >>
  `frame_call_value cx (if flags.rcf_is_static then NONE else SOME amount)
      (es with gas_obs := tail) =
    (INL (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount),
     es with gas_obs := tail)` by
    (Cases_on `cx.txn.is_static` >> Cases_on `flags.rcf_is_static` >>
     gvs[vyperInterpreterTheory.frame_call_value_def,vyperStateTheory.return_def,
       vyperStateTheory.check_def,vyperStateTheory.assert_def,
       vyperStateTheory.ignore_bind_def,vyperStateTheory.bind_def]) >>
  mp_tac (raw_call_source_oracle_action |> Q.INST [`es` |-> `es with gas_obs := tail`,
    `esf` |-> `es with gas_obs := tail`, `es1` |-> `ee with gas_obs := tail`,
    `value_opt` |-> `if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount`]) >>
  impl_tac >- (drule raw_call_prepared_source_domain >>
    disch_then (qspecl_then [`flags.rcf_is_static`, `amount`] strip_assume_tac) >>
    simp[raw_call_take_gas_obs] >> metis_tac[]) >>
  simp[raw_call_adopt_gas_obs] >>
  Cases_on `flags.rcf_revert_on_failure /\ ~outcome.co_success` >> simp[]
QED
