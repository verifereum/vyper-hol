(* Concrete NONE-mode tail contracts. These are facts about the existing
 * monadic expressions, not another evaluator. No oracle activation here.
 * TOP-LEVEL: concrete_extcall_tail, concrete_send_tail_frame.
 *)
Theory vyperCallFrame
Ancestors
  pair sum list option vyperState vyperInterpreter vyperStatePreservation
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";

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
     update_accounts_def, update_transient_def, append_logs_def,
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
       update_accounts_def, update_transient_def, append_logs_def, EQ_SYM_EQ]
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

(* Pre-TASK029 client proof fragments, retained for proof-history review.
   Live replacements use the named contracts above; no proof was admitted.

vyperEvalExprPreservesScopesDom: Send / ExtCall post-run continuation
  imp_res_tac transfer_value_scopes >>
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    first_x_assum drule
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ rw[]
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ gvs[check_def, type_check_def, assert_def, bind_def, COND_RATOR, CaseEq"bool",
           return_def, CaseEq"sum", CaseEq"prod", get_accounts_def,
           get_transient_storage_def]
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes \\ gvs[] )
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (pop_assum mp_tac \\ rw[update_accounts_def, return_def])
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (pop_assum mp_tac \\ rw[update_transient_def, return_def])
  \\ IF_CASES_TAC
  >- (
    strip_tac
    \\ last_x_assum $ funpow 2 drule_then drule
    \\ simp[]
    \\ rpt $ disch_then $ drule_at Any
    \\ gvs[]
    \\ rpt $ disch_then $ drule_at Any
    \\ gvs[ignore_bind_def]
    \\ disch_then $ drule_at Any
    \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
    \\ imp_res_tac update_accounts_scopes
    \\ imp_res_tac update_transient_scopes
    \\ imp_res_tac append_logs_scopes
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ strip_tac
    \\ gvs[append_logs_def, return_def, check_def, type_check_def, assert_def]
    \\ first_x_assum drule
    \\ first_x_assum drule
    \\ gvs[get_accounts_def, get_transient_storage_def, return_def,
           check_def, assert_def,
           COND_RATOR, CaseEq"bool", bind_def, CaseEq"sum", CaseEq"prod"]
    \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ gvs[])
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    first_x_assum drule
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ rw[] \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
    \\ imp_res_tac update_accounts_scopes
    \\ imp_res_tac update_transient_scopes
    \\ imp_res_tac append_logs_scopes
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ imp_res_tac lift_sum_scopes >> imp_res_tac lift_sum_runtime_scopes
    \\ gvs[get_accounts_def, get_transient_storage_def, return_def,
           COND_RATOR, CaseEq"bool", bind_def, CaseEq"sum", CaseEq"prod"]
    \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ gvs[assert_def] )
  \\ first_x_assum drule
  \\ first_x_assum(qspec_then`ARB`kall_tac)
  \\ rw[return_def] \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
  \\ imp_res_tac update_accounts_scopes
  \\ imp_res_tac update_transient_scopes
  \\ imp_res_tac append_logs_scopes
  \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
  \\ imp_res_tac lift_sum_scopes >> imp_res_tac lift_sum_runtime_scopes
  \\ gvs[get_accounts_def, get_transient_storage_def, return_def,
         COND_RATOR, CaseEq"bool", bind_def, CaseEq"sum", CaseEq"prod"]
  \\ imp_res_tac lift_sum_runtime_scopes
  \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
  \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
  \\ gvs[assert_def]

vyperEvalPreservesImmutablesDom: Send / extcall_inner_pipeline_imm_dom
  imp_res_tac transfer_value_immutables >> gvs[] >>
  rw[bind_def, ignore_bind_def, check_def, type_check_def, assert_def,
     update_accounts_def, update_transient_def, append_logs_def, return_def,

vyperEvalPreservesScopes: Send / mechanical loop_body rename
    imp_res_tac transfer_value_scopes >>
    imp_res_tac transfer_value_immutables >> gvs[] >>
    qspecl_then [`cx`, `body`, `nm`, `tyv`, `v`, `st`] mp_tac try_body_preserves_tl_dom >>
  (qspecl_then [`cx`, `body`, `nm`, `tyv`, `v`, `st`] mp_tac try_body_preserves_tl_dom >>

vyperLogPreservation: Send / ext_call_tail_log_extends
  imp_res_tac transfer_value_logs >> gvs[] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.update_accounts_def, vyperStateTheory.update_transient_def,
       vyperInterpreterTheory.append_logs_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
*)
