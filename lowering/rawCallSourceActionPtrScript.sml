(* Source-only oracle branch: framing and take failures stay explicit. *)
Theory rawCallSourceActionPtr
Ancestors vyperInterpreter vyperState vyperValue
  vyperCallOutcome vyperCallOutcomeProps extCallOracle

Theorem raw_call_source_oracle_action:
  ~flags.rcf_is_delegate /\ (~flags.rcf_is_static \/ amount = 0) /\
  frame_call_value cx (if flags.rcf_is_static then NONE else SOME amount) es =
    (INL value_opt,esf) /\ IS_SOME esf.outcomes /\
  take_call_outcome target data value_opt esf = (INL (rq,outcome),es1) ==>
  eval_raw_call cx flags target data amount gas es =
    (if flags.rcf_revert_on_failure /\ ~outcome.co_success then
       (INR (Error (RevertData outcome.co_returnData)),SND (adopt_call_outcome rq outcome es1))
     else
       (INL (Value (if flags.rcf_revert_on_failure then
          if flags.rcf_max_outsize = 0 then NoneV
          else BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)
        else if flags.rcf_max_outsize = 0 then BoolV outcome.co_success
        else ArrayV (TupleV [BoolV outcome.co_success;
          BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)]))),
        SND (adopt_call_outcome rq outcome es1)))
Proof
  strip_tac >> Cases_on `flags.rcf_is_static` >> gvs[] >>
  simp[vyperInterpreterTheory.eval_raw_call_def, vyperStateTheory.bind_def,
    vyperStateTheory.ignore_bind_def, vyperStateTheory.type_check_def,
    vyperStateTheory.assert_def, vyperStateTheory.return_def,
    vyperCallOutcomeTheory.adopt_call_outcome_equation] >>
  Cases_on `flags.rcf_revert_on_failure` >> Cases_on `outcome.co_success` >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

Theorem raw_call_static_value_abort:
  cx.txn.is_static /\ ~flags.rcf_is_delegate /\ ~flags.rcf_is_static /\
  amount <> 0 ==>
  eval_raw_call cx flags target data amount gas es =
    (INR (Error (RuntimeError "write in static context")), es)
Proof
  simp[eval_raw_call_def, frame_call_value_def, type_check_def,
       check_def, assert_def, bind_def, ignore_bind_def, vyperStateTheory.return_def]
QED

Theorem raw_call_source_oracle_take_error:
  ~flags.rcf_is_delegate /\ (~flags.rcf_is_static \/ amount = 0) /\
  frame_call_value cx (if flags.rcf_is_static then NONE else SOME amount) es =
    (INL value_opt,esf) /\ IS_SOME esf.outcomes /\
  take_call_outcome target data value_opt esf = (INR exc,es1) ==>
  eval_raw_call cx flags target data amount gas es = (INR exc,es1)
Proof
  strip_tac >> Cases_on `flags.rcf_is_static` >> gvs[] >>
  simp[vyperInterpreterTheory.eval_raw_call_def, vyperStateTheory.bind_def,
    vyperStateTheory.ignore_bind_def, vyperStateTheory.type_check_def,
    vyperStateTheory.assert_def, vyperStateTheory.return_def]
QED

Theorem raw_call_take_gas_obs:
  take_call_outcome target data value_opt (es with gas_obs := tail) =
    (FST (take_call_outcome target data value_opt es),
     SND (take_call_outcome target data value_opt es) with gas_obs := tail)
Proof
  simp[vyperCallOutcomeTheory.take_call_outcome_def,
    vyperCallOutcomeTheory.take_request_outcome_def,
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
  Cases_on `rq.cr_kind = MessageCall` >>
  Cases_on `rq.cr_kind = DelegateMessageCall` >> simp[]
QED

Theorem raw_call_eval_action:
  eval_expr cx (Call ann (RawCallTarget flags) args dflt) =
  bind (eval_exprs cx args) (\vs.
    do
      type_check (LENGTH vs = 2 + LENGTH flags.rcf_kws) "raw_call args";
      target <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
      data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_call data";
      amount <- lift_option_type (raw_call_value flags.rcf_kws (DROP 2 vs)) "raw_call value";
      eval_raw_call cx flags target data amount
        (forwarded_gas default_evm_gas_limit
          (ext_call_kwarg EKGas flags.rcf_kws (DROP 2 vs)))
    od)
Proof
  simp[Once evaluate_def]
QED

Theorem raw_call_source_continuation:
  dest_AddressV av = SOME target /\ LENGTH kvs = LENGTH flags.rcf_kws /\
  raw_call_value flags.rcf_kws kvs = SOME amount ==>
  (do
      type_check (LENGTH (av::BytesV bs::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
      target' <- lift_option_type (dest_AddressV (EL 0 (av::BytesV bs::kvs))) "raw_call target";
      data <- lift_option_type (dest_BytesV (EL 1 (av::BytesV bs::kvs))) "raw_call data";
      value <- lift_option_type (raw_call_value flags.rcf_kws (DROP 2 (av::BytesV bs::kvs))) "raw_call value";
      eval_raw_call cx flags target' data value
        (forwarded_gas default_evm_gas_limit
          (ext_call_kwarg EKGas flags.rcf_kws (DROP 2 (av::BytesV bs::kvs))))
   od) = eval_raw_call cx flags target bs amount
     (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs))
Proof
  strip_tac >> simp[type_check_def, assert_def, ignore_bind_def,
    lift_option_type_def, check_def, dest_BytesV_def] >>
  simp[FUN_EQ_THM, vyperStateTheory.bind_def, vyperStateTheory.assert_def,
    vyperStateTheory.return_def]
QED
