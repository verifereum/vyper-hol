(* Static call tails preserve the machine-visible evaluation state. *)
Theory vyperReadOnlyCalls
Ancestors
  vyperMachineFrame vyperStaticCallFrame vyperInterpreter vyperState
  vyperCallOutcome vyperCallOutcomeFrame vyperCallOutcomeProps
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";

Theorem run_raw_call_static_frame:
  flags.rcf_is_static /\ ~flags.rcf_is_delegate /\
  run_raw_call cx flags addr data amount accounts transient =
    SOME (ok,ret,accounts',transient',logs',deletions) ==>
  accounts' = accounts /\ transient' = transient /\ logs' = [] /\ deletions = []
Proof
  simp[run_raw_call_def] >> metis_tac[run_ext_call_static_frame]
QED

Theorem machine_frame_raw_call_active[local]:
  flags.rcf_is_static /\ ~flags.rcf_is_delegate /\ amount = 0 /\
  eval_raw_call cx flags addr data amount st = (res,st') ==>
  machine_frame st st'
Proof
  strip_tac >>
  gvs[eval_raw_call_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, get_accounts_def,
      get_transient_storage_def] >>
  Cases_on `run_raw_call cx flags addr data 0 st.accounts st.tStorage` >>
  gvs[lift_option_def, bind_def, return_def, raise_def, machine_frame_def] >>
  rename1 `run_raw_call _ _ _ _ _ _ _ = SOME call_result` >>
  PairCases_on `call_result` >>
  drule_all run_raw_call_static_frame >> strip_tac >> gvs[] >>
  Cases_on `flags.rcf_revert_on_failure` >> Cases_on `call_result0` >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  gvs[update_accounts_def, update_transient_def, append_logs_def,
      bind_def, ignore_bind_def, return_def, raise_def, machine_frame_def]
QED

Theorem machine_frame_raw_call:
  flags.rcf_is_static /\
  eval_raw_call cx flags addr data amount st = (res,st') ==>
  machine_frame st st'
Proof
  strip_tac >> Cases_on `~flags.rcf_is_delegate /\ amount = 0`
  >- metis_tac[machine_frame_raw_call_active] >>
  gvs[eval_raw_call_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, raise_def, machine_frame_def]
QED

Theorem machine_frame_static_oracle:
  state_rel_frame machine_frame
    (do
      (rq,outcome) <- take_call_outcome target data NONE;
      (if call_outcome_success outcome then return ()
       else raise $ Error $ RevertData $ call_outcome_return_data outcome);
      adopt_call_outcome rq outcome;
      return (call_outcome_return_data outcome)
    od)
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  Cases_on `take_call_outcome target data NONE st` >>
  rename1 `take_call_outcome _ _ _ _ = (answer,st1)` >>
  `machine_frame st st1` by
    (irule take_call_outcome_transport >> conj_tac >- simp[] >>
     goal_assum (drule_at Any)) >>
  Cases_on `answer` >-
    (rename1 `INL ro` >> PairCases_on `ro` >>
     drule take_call_outcome_success >> strip_tac >>
     gvs[call_outcome_request_def, bind_def, ignore_bind_def,
         adopt_call_outcome_equation, machine_frame_def] >>
     Cases_on `ro1.co_success` >>
     gvs[return_def, raise_def, machine_frame_def]) >>
  gvs[bind_def, ignore_bind_def, machine_frame_def]
QED

Theorem static_concrete_tail_frame:
  accounts = st.accounts /\
  (do
    tStorage <- get_transient_storage;
    result <- lift_option
      (run_ext_call caller target data NONE gas accounts tStorage txp)
      "ExtCall run failed";
    success <<- FST result; result1 <<- SND result;
    returnData <<- FST result1; result2 <<- SND result1;
    accounts' <<- FST result2; result3 <<- SND result2;
    tStorage' <<- FST result3; result4 <<- SND result3;
    emitted_logs <<- FST result4; deletions <<- SND result4;
    (if success then return () else raise $ Error $ RevertData returnData);
    update_accounts (K accounts');
    update_transient (K tStorage');
    append_logs emitted_logs;
    update_pending_deletions (APPEND deletions);
    return returnData
  od) st = (res,st') ==>
  machine_frame st st'
Proof
  strip_tac >> gvs[get_transient_storage_def, bind_def, return_def] >>
  Cases_on `run_ext_call caller target data NONE gas st.accounts st.tStorage txp` >>
  gvs[lift_option_def, bind_def, return_def, raise_def, machine_frame_def] >>
  rename1 `run_ext_call _ _ _ _ _ _ _ _ = SOME call_result` >>
  PairCases_on `call_result` >> drule run_ext_call_static_frame >>
  strip_tac >> gvs[] >> Cases_on `call_result0` >>
  gvs[ignore_bind_def, bind_def, update_accounts_def, update_transient_def,
      append_logs_def, return_def, raise_def, machine_frame_def]
QED

Theorem ext_call_decode_frame[local]:
  state_rel_frame machine_frame
    (case (if data = [] then default_opt else NONE) of
     | SOME v => do
         accounts <- get_accounts;
         check (skip \/ ext_call_has_code target accounts)
               "ExtCall target has no code";
         return (Value v)
       od
     | NONE => do
         v <- lift_sum_runtime (evaluate_abi_decode_return tenv ret_type data);
         return (Value v)
       od)
Proof
  Cases_on `if data = [] then default_opt else NONE` >>
  simp[state_rel_frame_def, get_accounts_def, check_def, assert_def,
       ignore_bind_def, bind_def, return_def, lift_sum_runtime_def] >>
  rpt gen_tac >> rpt CASE_TAC >> gvs[return_def, raise_def]
QED

Theorem ext_call_effects_static_frame[local]:
  machine_frame st
    (SND (eval_ext_call_effects cx target data NONE gas st.accounts st))
Proof
  simp[Once eval_ext_call_effects_def, Once bind_def, return_def] >>
  Cases_on `st.outcomes` >> simp[]
  >- (qmatch_goalsub_abbrev_tac `SND (tail st)` >>
      Cases_on `tail st` >> simp[] >>
      irule static_concrete_tail_frame >>
      simp[ignore_bind_def] >>
      qpat_x_assum `tail st = _` mp_tac >>
      simp[Abbr `tail`, ignore_bind_def] >> strip_tac >>
      goal_assum (drule_at Any)) >>
  simp[ignore_bind_def] >>
  irule (SRULE [state_rel_frame_def, ignore_bind_def]
               machine_frame_static_oracle)
QED

Theorem machine_frame_ext_call:
  eval_ext_call cx T skip sig opts vs st = (res,st') ==>
  machine_frame st st'
Proof
  `state_rel_frame machine_frame (eval_ext_call cx T skip sig opts vs)`
    suffices_by metis_tac[state_rel_frame_at] >>
  PairCases_on `sig` >> Cases_on `vs`
  >- simp[eval_ext_call_def, machine_frame_primitives] >>
  simp[Once eval_ext_call_def, state_rel_frame_def, ignore_bind_def] >>
  gen_tac >>
  simp[Once bind_def, type_check_def, assert_def] >>
  IF_CASES_TAC >> simp[raise_def, return_def] >>
  simp[Once bind_def, lift_option_type_def] >>
  Cases_on `dest_AddressV h` >> simp[raise_def, return_def] >>
  simp[Once bind_def, return_def] >>
  simp[Once bind_def, lift_option_type_def] >>
  qmatch_goalsub_abbrev_tac `build_ext_calldata tenv _ _ args` >>
  Cases_on `build_ext_calldata tenv sig0 sig1 args` >>
  simp[return_def, raise_def] >>
  simp[Once bind_def, get_accounts_def, return_def] >>
  simp[Once bind_def, check_def, assert_def] >>
  IF_CASES_TAC >> simp[return_def, raise_def] >>
  irule state_rel_bind_pointwise >> rpt conj_tac
  >- (rpt strip_tac >> BETA_TAC >>
      irule (SRULE [state_rel_frame_def, check_def, ignore_bind_def]
                   ext_call_decode_frame))
  >- simp[machine_frame_def] >>
  simp[ext_call_effects_static_frame]
QED
