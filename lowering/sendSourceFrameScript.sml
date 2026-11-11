Theory sendSourceFrame
Ancestors
  vyperInterpreter vyperState vyperCallOutcome

(* Only Value NoneV reaches the continuation of send.  Restricting the
   continuation premise avoids imposing frames on unrelated read results. *)
Theorem send_bind_gas_frame:
  (!s r t. k (Value NoneV) s = (r,t) ==>
     t.gas_obs = s.gas_obs /\
     !gs. k (Value NoneV) (s with gas_obs := gs) =
          (r,t with gas_obs := gs)) ==>
  !cx has_gas vs s r t.
    vyperState$bind (eval_send cx has_gas vs) k s = (r,t) ==>
    t.gas_obs = s.gas_obs /\
    !gs. vyperState$bind (eval_send cx has_gas vs) k
           (s with gas_obs := gs) = (r,t with gas_obs := gs)
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `vs` >> simp[eval_send_def, bind_def, raise_def] >>
  Cases_on `t'` >> simp[eval_send_def, bind_def, raise_def] >>
  Cases_on `LENGTH t'' = if has_gas then 1 else 0` >>
  Cases_on `dest_AddressV h` >> Cases_on `dest_NumV h'` >>
  simp[ignore_bind_def, bind_def, type_check_def, lift_option_type_def,
       lift_option_def, check_def, assert_def, return_def, raise_def,
       frame_call_value_def, get_accounts_def, get_transient_storage_def,
       update_accounts_def, update_transient_def, append_logs_def,
       update_pending_deletions_def,
       take_call_outcome_def, take_request_outcome_def, call_outcome_request_def,
       adopt_call_outcome_def] >>
  Cases_on `cx.txn.is_static` >> Cases_on `x' = 0` >>
  simp[ignore_bind_def, bind_def, assert_def, return_def] >>
  Cases_on `s.outcomes` >>
  simp[ignore_bind_def, bind_def, get_accounts_def, get_transient_storage_def,
       take_call_outcome_def, take_request_outcome_def, call_outcome_request_def] >>
  simp[return_def, raise_def, assert_def, update_accounts_def,
       update_pending_deletions_def,
       update_transient_def, append_logs_def, adopt_call_outcome_def,
       bind_def, ignore_bind_def]
  >>~- ([`s.outcomes = NONE`],
    qpat_abbrev_tac `run_result = run_ext_call _ _ _ _ _ _ _ _` >>
    Cases_on `run_result` >> simp[return_def, raise_def] >>
    rename1 `FST result` >> Cases_on `FST result` >> simp[] >>
    strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_abbrev_tac `taken = take_outcome _ _` >>
  PairCases_on `taken` >>
  simp[ignore_bind_def, bind_def, assert_def, adopt_call_outcome_def,
       return_def] >>
  Cases_on `taken0.co_success` >>
  Cases_on `accounts_runtime_well_typed taken0.co_accounts` >>
  simp[ignore_bind_def, bind_def, assert_def, adopt_call_outcome_def,
       return_def] >>
  simp[pairTheory.UNCURRY] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `!s r t. _` imp_res_tac >> fs[]
QED
