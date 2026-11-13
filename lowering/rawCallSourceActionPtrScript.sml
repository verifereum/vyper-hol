(* Source-only oracle branch: framing and take failures stay explicit. *)
Theory rawCallSourceActionPtr
Ancestors vyperInterpreter vyperCallOutcome vyperCallOutcomeProps extCallOracle

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
