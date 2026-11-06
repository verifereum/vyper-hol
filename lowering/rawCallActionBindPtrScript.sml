(* Bind the evaluated operands to the source raw-call continuation.
   Keep gas observations in the action: implicit machine GAS is not a source keyword. *)
Theory rawCallActionBindPtr
Ancestors
  rawCallPrefixReadyPtr gasSummaryComposePtr gasExemptCert stmtSimForRounds
  vyperInterpreter vyperState vyperValue

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

Theorem raw_call_marked_continuation_admissible:
  gas_admissible (eval_expr cx (Call ann (RawCallTarget flags) args dflt)) expr_vv_res_ok es /\
  gas_marked_exec F (ctx,func) (eval_exprs cx args) (es,s) marks
    (INL (av::BytesV bs::kvs)) mid (OK t) /\
  dest_AddressV av = SOME target /\ LENGTH kvs = LENGTH flags.rcf_kws /\
  raw_call_value flags.rcf_kws kvs = SOME amount ==>
  gas_admissible (eval_raw_call cx flags target bs amount
    (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs)))
    expr_vv_res_ok (mid with gas_obs := [])
Proof
  rewrite_tac[raw_call_eval_action, gasSummaryTheory.gas_marked_exec_def] >>
  strip_tac >> drule_all gas_admissible_bind_tail >>
  BETA_TAC >> drule_all raw_call_source_continuation >>
  disch_then (qspecl_then [`cx`, `bs`] SUBST1_TAC) >> simp[]
QED
