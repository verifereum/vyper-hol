(* Concrete NONE-mode tail contracts. These are facts about the existing
 * monadic expressions, not another evaluator. No oracle activation here.
 * TOP-LEVEL: concrete_extcall_tail, concrete_send_tail_frame.
 *)
Theory vyperCallFrame
Ancestors
  pair sum list option vyperState vyperInterpreter vyperStatePreservation
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";

Theorem eval_ext_call_success_value:
  eval_ext_call cx static skip sigt opts vs st = (INL pv,st') ==>
  ?v. pv = Value v
Proof
  PairCases_on `sigt` >> Cases_on `vs` >>
  simp[eval_ext_call_def, frame_call_value_def, COND_RATOR, bind_apply, ignore_bind_apply,
       lift_option_type_def, type_check_def, check_def, assert_def,
       return_def, raise_def, get_accounts_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `eval_ext_call_effects ca cb cc cd ce cf cg` >>
  Cases_on `eval_ext_call_effects ca cb cc cd ce cf cg` >>
  gvs[bind_apply, ignore_bind_apply, lift_sum_runtime_def,
      return_def, raise_def, get_accounts_def, check_def, assert_def,
      AllCaseEqs()] >>
  Cases_on `if returnData = [] then
    ext_call_kwarg EKDefault opts (DROP (LENGTH sigt1) t) else NONE` >>
  gvs[bind_apply, ignore_bind_apply, return_def, raise_def,
      get_accounts_def, assert_def, AllCaseEqs()] >>
  Cases_on `evaluate_abi_decode_return (get_tenv ca) sigt2 returnData` >>
  gvs[bind_apply, return_def, raise_def]
QED

Theorem eval_send_success_value:
  eval_send cx has_gas vs st = (INL pv,st') ==> ?v. pv = Value v
Proof
  Cases_on `vs` >- simp[eval_send_def, raise_def] >>
  Cases_on `t` >- simp[eval_send_def, raise_def] >>
  Cases_on `dest_AddressV h` >> Cases_on `dest_NumV h'` >>
  simp[eval_send_def, frame_call_value_def, COND_RATOR, bind_apply, ignore_bind_apply, type_check_def,
       check_def, assert_def, return_def, raise_def, lift_option_type_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
  Cases_on `st.outcomes` >>
  gvs[bind_apply, ignore_bind_apply, return_def, raise_def, AllCaseEqs(),
      get_accounts_def, get_transient_storage_def, lift_option_def,
      bind_def, ignore_bind_def, check_def, assert_def] >>
  rpt strip_tac >> gvs[] >>
  (* static frame: the outcomes case is on the post-check state *)
  TRY (qpat_x_assum `option_CASE _ _ _ _ = _` mp_tac >> CASE_TAC >>
       simp[bind_apply, ignore_bind_apply, return_def, raise_def,
            AllCaseEqs(), get_accounts_def, get_transient_storage_def,
            lift_option_def, bind_def, ignore_bind_def, check_def,
            assert_def] >>
       rpt strip_tac >> gvs[]) >>
  pairarg_tac >> gvs[bind_def, ignore_bind_def, check_def, assert_def,
                       return_def, raise_def, AllCaseEqs()]
QED

Theorem eval_raw_call_success_value:
  eval_raw_call cx flags addr data amount gas st = (INL pv,st') ==>
  ?v. pv = Value v
Proof
  (* Only the final return builds pv: keep the call steps folded. *)
  simp[eval_raw_call_def, bind_def, ignore_bind_def, return_def, raise_def,
       COND_RATOR, AllCaseEqs(), UNCURRY, LET_THM] >>
  rw[] >> gvs[]
QED

Theorem concrete_extcall_tail:
  (do
    check success msg;
    update_accounts (K accounts);
    update_transient (K transient);
    append_logs logs;
    k
  od) st =
  if success then
    k (st with <|accounts := accounts; tStorage := transient;
                 logs := st.logs ++ logs|>)
  else (INR (Error (RuntimeError msg)),st)
Proof
  rw[bind_def, ignore_bind_def, check_def, assert_def,
     update_accounts_def, update_transient_def, append_logs_def, update_pending_deletions_def,
     return_def, raise_def]
QED

Theorem concrete_extcall_value_state:
  (if isc then return (NONE,TL vs)
   else do
     type_check (TL vs <> []) "ExtCall no value";
     v <- lift_option_type (dest_NumV (HD (TL vs))) "ExtCall value not int";
     return (SOME v,TL (TL vs))
   od) st = (res,st') ==> st' = st
Proof
  Cases_on `isc` >>
  rw[bind_def, ignore_bind_def, type_check_def, assert_def,
     lift_option_type_def, return_def, raise_def] >>
  Cases_on `dest_NumV (HD (TL vs))` >> gvs[return_def, raise_def]
QED

(* Generated evaluator IHs mention the individual successful steps. Expose
   their exact equations at one boundary, without unfolding them in clients. *)
Theorem concrete_extcall_tail_cases:
  (do check success msg;
      update_accounts (K accounts);
      update_transient (K transient);
      append_logs logs; k od) st = (res,st') <=>
  (~success /\ res = INR (Error (RuntimeError msg)) /\ st' = st) \/
  (success /\ ?sa sb sc.
    check success msg st = (INL (),st) /\
    update_accounts (K accounts) st = (INL (),sa) /\
    update_transient (K transient) sa = (INL (),sb) /\
    append_logs logs sb = (INL (),sc) /\ k sc = (res,st') /\
    sa.scopes = st.scopes /\ sb.scopes = st.scopes /\
    sc.scopes = st.scopes /\
    sa.immutables = st.immutables /\ sb.immutables = st.immutables /\
    sc.immutables = st.immutables)
Proof
  Cases_on `success` >>
  simp[concrete_extcall_tail, check_def, assert_def, return_def,
       update_accounts_def, update_transient_def, append_logs_def, update_pending_deletions_def, EQ_SYM_EQ]
QED

(* Reusable relation transport, keeping default/decode in k. *)
Theorem concrete_extcall_tail_transport:
  (!s. R s s) /\
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!s accounts transient logs.
    R s (s with <|accounts := accounts; tStorage := transient;
                  logs := s.logs ++ logs|>)) /\
  (success ==> !s res t. k s = (res,t) ==> R s t) /\
  (do check success msg;
      update_accounts (K accounts);
      update_transient (K transient);
      append_logs logs; k od) st = (res,st') ==>
  R st st'
Proof
  simp[concrete_extcall_tail] >> Cases_on `success` >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> strip_tac >>
  qpat_x_assum `!s t u. _` irule >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Consumers need these projections, rather than a relation API matrix. *)
Theorem concrete_send_step_locals:
  transfer_value fromAddr toAddr amount st = (res,st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables /\
  st'.logs = st.logs
Proof
  rpt strip_tac >> qpat_x_assum `transfer_value _ _ _ _ = _` mp_tac >>
  rw[transfer_value_def, bind_def, ignore_bind_def,
     get_accounts_def, check_def, assert_def, update_accounts_def,
     return_def, raise_def] >> gvs[AllCaseEqs()]
QED

(* Both rejection checks are runtime failures; transfer cannot manufacture
   source TypeError or control exceptions. *)
Theorem concrete_send_error:
  transfer_value fromAddr toAddr amount st = (INR exc,st') ==>
  (exc = Error (RuntimeError "transfer_value amount") \/
   exc = Error (RuntimeError "transfer_value recipient overflow")) /\ st' = st
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def,
     check_def, assert_def, update_accounts_def, return_def, raise_def] >>
  gvs[AllCaseEqs()]
QED

Theorem concrete_send_tail_frame:
  (do transfer_value fromAddr toAddr amount; return (Value NoneV) od) st =
    (res,st') ==>
  st' = st with accounts := st'.accounts
Proof
  simp[bind_def, ignore_bind_def, return_def] >>
  Cases_on `transfer_value fromAddr toAddr amount st` >>
  rename1 `transfer_value fromAddr toAddr amount st = (answer,st1)` >>
  Cases_on `answer` >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `transfer_value _ _ _ _ = _` mp_tac >>
  rw[transfer_value_def, bind_def, ignore_bind_def,
     get_accounts_def, check_def, assert_def, update_accounts_def,
     return_def, raise_def] >>
  gvs[AllCaseEqs(), evaluation_state_component_equality]
QED

