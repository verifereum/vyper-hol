(* Total source normalization and counted finish assembly. *)
Theory rawCallFinishTotalPtr
Ancestors
  rawCallFinishStepPtr rawCallFinishCodePtr rawCallFinishSuffixPtr
  rawCallSourceDomainPtr rawCallSourceActionPtr gasSummary exprSimOperands
  exprLoweringProps bodyPtrDefs wordArgsPtr exprSimWordArgs
  emitHelperProps fragGasPathPtr

Theorem raw_call_take_gas_obs:
  take_call_outcome target data value_opt (es with gas_obs := tail) =
    (FST (take_call_outcome target data value_opt es),
     SND (take_call_outcome target data value_opt es) with gas_obs := tail)
Proof
  simp[vyperCallOutcomeTheory.take_call_outcome_def,
    vyperCallOutcomeTheory.call_outcome_request_def] >>
  Cases_on `es.outcomes` >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem raw_call_adopt_gas_obs:
  adopt_call_outcome rq outcome (es with gas_obs := tail) =
    (FST (adopt_call_outcome rq outcome es),
     SND (adopt_call_outcome rq outcome es) with gas_obs := tail)
Proof
  simp[vyperCallOutcomeTheory.adopt_call_outcome_equation] >>
  Cases_on `rq.cr_static` >> Cases_on `outcome.co_success` >>
  Cases_on `rq.cr_kind = MessageCall` >> simp[]
QED

Theorem raw_call_prepared_source_total:
  stmt_state_rel ctx func cenv cx es s /\ expr_sim_inv cenv cx env es /\
  ~flags.rcf_is_delegate /\
  gas_admissible (eval_raw_call cx flags target data amount gas) expr_vv_res_ok es ==>
  ?rq outcome es1.
    take_call_outcome target data (if flags.rcf_is_static then NONE else SOME amount) es =
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
  drule_all raw_call_prepared_take_success >>
  disch_then (qspecl_then [`if flags.rcf_is_static then NONE else SOME amount`,
    `target`, `data`] strip_assume_tac) >>
  qexistsl_tac [`rq`, `outcome`, `ee`] >> simp[] >> gen_tac >>
  mp_tac (raw_call_source_oracle_action |> Q.INST [`es` |-> `es with gas_obs := tail`,
    `esf` |-> `es with gas_obs := tail`, `es1` |-> `ee with gas_obs := tail`,
    `value_opt` |-> `if flags.rcf_is_static then NONE else SOME amount`]) >>
  impl_tac >- (drule raw_call_prepared_source_domain >>
    disch_then (qspecl_then [`flags.rcf_is_static`, `amount`] strip_assume_tac) >>
    gvs[vyperInterpreterTheory.frame_call_value_def, vyperStateTheory.return_def,
      raw_call_take_gas_obs] >> metis_tac[]) >>
  simp[raw_call_adopt_gas_obs] >>
  Cases_on `flags.rcf_revert_on_failure /\ ~outcome.co_success` >> simp[]
QED


Theorem raw_call_case_emit_facts:
  (case (if stat then StaticCall else RegularCall) of
     RegularCall => emit_op CALL [gas_op;addr;value_op;dp;dl;op;rz_op]
   | DelegateCall => emit_op DELEGATECALL [gas_op;addr;dp;dl;op;rz_op]
   | StaticCall => emit_op STATICCALL [gas_op;addr;dp;dl;op;rz_op]) sa = (result,sc) /\
  fn_has_code sa sc func ==>
  ?out. result = Var out /\ ~not_fresh_at sa out
Proof
  Cases_on `stat` >> simp[] >> strip_tac >>
  drule_all raw_call_emit_code >> metis_tac[]
QED

