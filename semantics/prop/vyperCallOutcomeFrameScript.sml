(* Oracle tail property transport. Whole-record facts supply the boundary;
 * R can be a residual frame, scope/type-value frame, or log-prefix relation.
 * No purity/storage claim about external payloads and no typing premise on os.
 * This owner remains below Interpreter and TypeSystem.
 *)
Theory vyperCallOutcomeFrame
Ancestors
  pair sum list option vyperState vyperCallOutcome vyperCallOutcomeProps vyperCallOutcomeBranches
  vyperRuntimeAccounts extCallOracle
Libs monadsyntax

(* Keep underconstrained client monads in the source state/exception type. *)
val () = monadsyntax.enable_monad "vyper_evaluation";
val () = Parse.type_abbrev ("exception", ``:vyperState$exception``);
val _ = hide "body";

(* Guarded monadic transport retains the actual success equations used by
   evaluate_ind, including consuming default-return continuations. *)
Definition state_rel_frame_def:
  state_rel_frame R f <=> !st. R st (SND (f st))
End

Theorem state_rel_frame_result:
  state_rel_frame R f <=> !st res st'. f st = (res,st') ==> R st st'
Proof
  simp[state_rel_frame_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then `st` mp_tac) >> simp[]) >>
  first_x_assum (qspecl_then [`st`,`FST (f st)`,`SND (f st)`] mp_tac) >> simp[]
QED

Theorem state_rel_frame_at:
  state_rel_frame R f /\ f st = (res,st') ==> R st st'
Proof
  simp[state_rel_frame_result]
QED

Theorem state_rel_frame_bind_guarded:
  (!s t u. R s t /\ R t u ==> R s u) /\
  state_rel_frame R f /\
  (!s v t. f s = (INL v,t) ==> state_rel_frame R (g v)) ==>
  state_rel_frame R (vyperState$bind f g)
Proof
  simp[state_rel_frame_def, bind_def] >> rpt strip_tac >>
  Cases_on `f st` >> Cases_on `q` >> gvs[] >>
  `R st r` by
    (qpat_x_assum `!st. R st (SND (f st))` (qspec_then `st` mp_tac) >> simp[]) >>
  TRY (qpat_x_assum `!s v t. _` (qspecl_then [`st`,`x`,`r`] mp_tac) >>
    simp[] >> disch_then (qspec_then `r` mp_tac) >>
    strip_tac >> qpat_x_assum `!s t u. _` drule_all >> simp[])
QED

Theorem state_rel_frame_read:
  (!s. R s s) ==> state_rel_frame R (λst. vyperState$return (g st) st)
Proof
  simp[state_rel_frame_def, return_def]
QED

(* Shared local-frame kit for evaluator properties which depend only on
   scopes/immutables. Account/storage/log/oracle effects remain unrestricted. *)
Theorem state_rel_frame_locals_primitives:
  (!s t. t.scopes = s.scopes /\ t.immutables = s.immutables ==> R s t) ==>
  state_rel_frame R (vyperState$return v) /\
  state_rel_frame R (λs. vyperState$return (g s) s) /\
  state_rel_frame R (vyperState$raise e) /\
  state_rel_frame R (type_check b msg) /\ state_rel_frame R (check b msg) /\
  state_rel_frame R (lift_option opt msg) /\
  state_rel_frame R (lift_option_type opt msg) /\
  state_rel_frame R (lift_sum_runtime rs) /\
  state_rel_frame R get_accounts /\ state_rel_frame R get_transient_storage /\
  state_rel_frame R (update_accounts upd) /\
  state_rel_frame R (update_transient upd_t) /\
  state_rel_frame R (update_pending_deletions deletions_upd) /\
  state_rel_frame R (λs. vyperState$return () (s with logs updated_by logs_upd)) /\
  state_rel_frame R (λs. vyperState$return () (s with logs := s.logs ++ logs)) /\
  state_rel_frame R (adopt_call_outcome rq co)
Proof
  strip_tac >>
  simp[state_rel_frame_def, return_def, raise_def, check_def, type_check_def,
       assert_def, lift_option_def, lift_option_type_def, lift_sum_runtime_def,
       get_accounts_def, get_transient_storage_def, update_accounts_def,
       update_transient_def, update_pending_deletions_def,
       adopt_call_outcome_equation] >>
  rpt strip_tac >> rpt CASE_TAC >> simp[return_def, raise_def]
QED

Theorem state_rel_frame_locals_take:
  (!s t. t.scopes = s.scopes /\ t.immutables = s.immutables ==> R s t) ==>
  state_rel_frame R (take_call_outcome target calldata value_opt)
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  drule take_call_outcome_frame >>
  simp[evaluation_state_component_equality] >> strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem take_call_outcome_transport:
  (!s os rqs. R s (s with <|outcomes := os; requests := rqs|>)) /\
  take_call_outcome target calldata value_opt st = (res,st') ==>
  R st st'
Proof
  rpt strip_tac >> drule take_call_outcome_frame >> strip_tac >>
  qpat_x_assum `!s os rqs. _` (qspecl_then
    [`st`,`st'.outcomes`,`st'.requests`] mp_tac) >> metis_tac[]
QED

Theorem adopt_call_outcome_transport:
  (!s. R s s) /\
  (!s accounts transient logs deletions.
    R s (s with <|accounts := accounts; tStorage := transient;
                  logs := s.logs ++ logs;
                  pending_deletions := deletions ++ s.pending_deletions|>)) /\
  adopt_call_outcome rq outcome st = (res,st') ==>
  R st st'
Proof
  rw[adopt_call_outcome_equation] >> gvs[]
QED

Theorem checked_call_outcome_transport:
  (!s. R s s) /\
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!s os rqs. R s (s with <|outcomes := os; requests := rqs|>)) /\
  (!s accounts transient logs deletions.
    R s (s with <|accounts := accounts; tStorage := transient;
                  logs := s.logs ++ logs;
                  pending_deletions := deletions ++ s.pending_deletions|>)) /\
  (!bs s res t. k bs s = (res,t) ==> R s t) /\
  (do
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success msg;
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = (res,st') ==>
  R st st'
Proof
  simp[checked_call_outcome_cases] >> rpt strip_tac >>
  drule_all take_call_outcome_transport >> strip_tac >>
  TRY (gvs[] >> NO_TAC) >>
  `R st1 st2` by
    (irule adopt_call_outcome_transport >>
     simp[evaluation_state_fupdcanon] >>
     qexistsl_tac [`outcome`,`INL ()`,`rq`] >> simp[]) >>
  qpat_x_assum `!bs s res t. _` drule >> strip_tac >>
  metis_tac[]
QED

(* The actual TASK028 continuation equations isolate the pre-take code check. *)
(* Retained for storage/suffix clients. Prove the legacy checked-tail
   equation locally: main no longer exports ExtCall_outcome_continue. *)
Theorem ExtCall_outcome_checked_tail:
  (do
    accounts <- get_accounts;
    (if ret_type = NoneT then
       check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success "ExtCall reverted";
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st =
  if ret_type = NoneT /\ NULL (lookup_account target st.accounts).code then
    (INR (Error (RuntimeError "ExtCall target has no code")),st)
  else (do
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success "ExtCall reverted";
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st
Proof
  Cases_on `ret_type = NoneT` >>
  Cases_on `NULL (lookup_account target st.accounts).code` >>
  simp[bind_def, ignore_bind_def, get_accounts_def, check_def, assert_def,
       return_def, raise_def]
QED

Theorem ExtCall_outcome_transport:
  (!s. R s s) /\
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!s os rqs. R s (s with <|outcomes := os; requests := rqs|>)) /\
  (!s accounts transient logs deletions.
    R s (s with <|accounts := accounts; tStorage := transient;
                  logs := s.logs ++ logs;
                  pending_deletions := deletions ++ s.pending_deletions|>)) /\
  (!bs s res t. k bs s = (res,t) ==> R s t) /\
  (do
    accounts <- get_accounts;
    (if ret_type = NoneT then
       check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success "ExtCall reverted";
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = (res,st') ==>
  R st st'
Proof
  REWRITE_TAC [ExtCall_outcome_checked_tail] >>
  Cases_on `ret_type = NoneT /\ NULL (lookup_account target st.accounts).code` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  drule_all (checked_call_outcome_transport |>
    SRULE [evaluation_state_fupdcanon]) >> simp[]
QED

Theorem Send_outcome_transport:
  (!s. R s s) /\
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!s os rqs. R s (s with <|outcomes := os; requests := rqs|>)) /\
  (!s accounts transient logs deletions.
    R s (s with <|accounts := accounts; tStorage := transient;
                  logs := s.logs ++ logs;
                  pending_deletions := deletions ++ s.pending_deletions|>)) /\
  (do
    (rq,outcome) <- take_call_outcome target [] (SOME amount);
    check outcome.co_success "send failed";
    adopt_call_outcome rq outcome;
    return (Value NoneV)
  od) st = (res,st') ==>
  R st st'
Proof
  rpt strip_tac >>
  irule (checked_call_outcome_transport |> INST_TYPE [alpha |-> ``:eval_result``]) >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`[]`,`\bs. vyperState$return (Value NoneV)`,
    `"send failed"`,`res`,`target`,`SOME amount`] >> simp[return_def]
QED

(* Locals are genuine residual fields, not protected adopted storage. *)
Theorem checked_call_outcome_locals:
  (!bs s res t. k bs s = (res,t) ==>
     t.scopes = s.scopes /\ t.immutables = s.immutables) /\
  (do
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success msg;
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = (res,st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables
Proof
  rpt strip_tac >>
  drule_all (checked_call_outcome_transport |> Q.INST
    [`R` |-> `\s t. t.scopes = s.scopes /\ t.immutables = s.immutables`]
    |> SRULE []) >> simp[]
QED

(* Exact effects at the continuation entry, including guard-owned typing.
   Failed/static adoption does not install payloads. The suffix is the actual
   shared take suffix, not an unconstrained future oracle. *)
Theorem take_adopt_call_outcome_effects:
  take_call_outcome target calldata value_opt st = (INL (rq,outcome),st1) /\
  adopt_call_outcome rq outcome st1 = (INL (),st2) ==>
  ?os rest prefix.
    st.outcomes = SOME os /\ st2.outcomes = SOME rest /\
    os = prefix ++ rest /\ LENGTH prefix <= 1 /\
    rq = call_outcome_request target calldata value_opt st /\
    st2.requests = record_request rq st.requests /\
    st2 = st with <|outcomes := SOME rest;
                   requests := record_request rq st.requests;
                   accounts := st2.accounts; tStorage := st2.tStorage;
                   logs := st2.logs;
                   pending_deletions := st2.pending_deletions|> /\
    (outcome.co_success /\ ~rq.cr_static ==>
      st2.accounts = outcome.co_accounts /\
      st2.tStorage = outcome.co_tStorage /\
      st2.logs = st.logs ++ outcome.co_logs /\
      st2.pending_deletions = outcome.co_toDelete ++ st.pending_deletions /\
      accounts_runtime_well_typed st2.accounts) /\
    (rq.cr_static \/ ~outcome.co_success ==>
      st2.accounts = st.accounts /\ st2.tStorage = st.tStorage /\
      st2.logs = st.logs /\ st2.pending_deletions = st.pending_deletions) /\
    (computed_precompile rq ==> prefix = [] /\ st2.requests = st.requests)
Proof
  rpt strip_tac >> drule_all checked_call_outcome_success_frame >> strip_tac >>
  drule take_call_outcome_success >> strip_tac >>
  drule_all take_call_outcome_suffix >> strip_tac >>
  gvs[adopt_call_outcome_equation] >>
  qexistsl_tac [`rest`,`prefix`] >>
  IF_CASES_TAC >> gvs[evaluation_state_component_equality]
QED
