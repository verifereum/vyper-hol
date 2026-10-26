(* Equations and frame facts for the call-outcome oracle boundary.
 * TOP-LEVEL: take_call_outcome_success, take_call_outcome_error,
 * take_call_outcome_suffix, take_adopt_call_outcome_typed.
 *)
Theory vyperCallOutcomeProps
Ancestors
  arithmetic list option pair sum
  extCallOracle vyperState vyperValue vyperRuntimeAccounts vyperCallOutcome

(* ===== Exact equations ===== *)

Theorem take_call_outcome_NONE:
  st.outcomes = NONE ==>
  take_call_outcome target calldata value_opt st =
    (INR (Error (RuntimeError "take_call_outcome")), st)
Proof
  simp[take_call_outcome_def]
QED

Theorem take_call_outcome_SOME:
  st.outcomes = SOME os /\
  rq = call_outcome_request target calldata value_opt st /\
  take_outcome rq os = (outcome, rest) ==>
  take_call_outcome target calldata value_opt st =
    (if outcome.co_success /\ ~rq.cr_static /\
        ~accounts_runtime_well_typed outcome.co_accounts
     then INR (Error (RuntimeError "call outcome accounts"))
     else INL (rq, outcome),
     st with <|outcomes := SOME rest;
               requests := record_request rq st.requests|>)
Proof
  rpt strip_tac >> gvs[take_call_outcome_def] >> rw[] >> gvs[]
QED

Theorem take_call_outcome_ordinary:
  st.outcomes = SOME (outcome::rest) /\
  rq = call_outcome_request target calldata value_opt st /\
  ~computed_precompile rq ==>
  take_call_outcome target calldata value_opt st =
    (if outcome.co_success /\ ~rq.cr_static /\
        ~accounts_runtime_well_typed outcome.co_accounts
     then INR (Error (RuntimeError "call outcome accounts"))
     else INL (rq, outcome),
     st with <|outcomes := SOME rest; requests := st.requests ++ [rq]|>)
Proof
  rpt strip_tac >> gvs[take_call_outcome_def, take_outcome_def, record_request_def] >>
  rw[] >> gvs[]
QED

Theorem take_call_outcome_exhausted:
  st.outcomes = SOME [] /\
  rq = call_outcome_request target calldata value_opt st /\
  ~computed_precompile rq ==>
  take_call_outcome target calldata value_opt st =
    (INL (rq, failed_outcome rq),
     st with <|outcomes := SOME []; requests := st.requests ++ [rq]|>)
Proof
  rpt strip_tac >> gvs[take_call_outcome_def, take_outcome_def, record_request_def]
QED

Theorem take_call_outcome_computed_valid:
  st.outcomes = SOME os /\
  rq = call_outcome_request target calldata value_opt st /\
  rq.cr_value = 0 /\
  precompile_result rq.cr_target rq.cr_data = SOME (SOME bs) ==>
  take_call_outcome target calldata value_opt st =
    (if ~rq.cr_static /\ ~accounts_runtime_well_typed st.accounts
     then INR (Error (RuntimeError "call outcome accounts"))
     else INL (rq, failed_outcome rq with
                       <|co_success := T; co_returnData := bs|>), st)
Proof
  rpt strip_tac >>
  gvs[take_call_outcome_def, take_outcome_def, record_request_def,
      computed_precompile_def, failed_outcome_def, call_outcome_request_def] >>
  rw[] >> gvs[evaluation_state_component_equality]
QED

Theorem take_call_outcome_computed_invalid:
  st.outcomes = SOME os /\
  rq = call_outcome_request target calldata value_opt st /\
  rq.cr_value = 0 /\ precompile_result rq.cr_target rq.cr_data = SOME NONE ==>
  take_call_outcome target calldata value_opt st = (INL (rq, failed_outcome rq), st)
Proof
  rpt strip_tac >>
  gvs[take_call_outcome_def, take_outcome_def, record_request_def,
      computed_precompile_def, call_outcome_request_def, evaluation_state_component_equality]
QED

(* ===== Whole-record frame and guarded typing ===== *)

(* Failed CREATE outcomes retain their account/transient snapshots. Only
   failed message calls, or any static request, leave the whole state alone. *)
Theorem adopt_call_outcome_static_failed:
  (rq.cr_static \/ (rq.cr_kind = MessageCall /\ ~outcome.co_success)) ==>
  adopt_call_outcome rq outcome st = (INL (),st)
Proof
  rw[adopt_call_outcome_equation, adopt_outcome_deletions_def] >>
  gvs[evaluation_state_component_equality]
QED

Theorem take_call_outcome_guard_rejected:
  st.outcomes = SOME os /\
  rq = call_outcome_request target calldata value_opt st /\
  take_outcome rq os = (outcome,rest) /\
  outcome.co_success /\ ~rq.cr_static /\
  ~accounts_runtime_well_typed outcome.co_accounts ==>
  take_call_outcome target calldata value_opt st =
    (INR (Error (RuntimeError "call outcome accounts")),
     st with <|outcomes := SOME rest;
               requests := record_request rq st.requests|>)
Proof
  rpt strip_tac >> drule_all take_call_outcome_SOME >> simp[]
QED

Theorem take_call_outcome_error:
  take_call_outcome target calldata value_opt st = (INR exc, st') ==>
  exc = Error (RuntimeError "take_call_outcome") \/
  exc = Error (RuntimeError "call outcome accounts")
Proof
  Cases_on `st.outcomes` >> simp[take_call_outcome_def] >>
  pairarg_tac >> rw[] >> gvs[]
QED

Theorem take_call_outcome_no_type_error_control:
  FST (take_call_outcome target calldata value_opt st) <> INR (Error (TypeError msg)) /\
  FST (take_call_outcome target calldata value_opt st) <> INR (AssertException msg) /\
  FST (take_call_outcome target calldata value_opt st) <> INR BreakException /\
  FST (take_call_outcome target calldata value_opt st) <> INR ContinueException /\
  FST (take_call_outcome target calldata value_opt st) <> INR (ReturnException v)
Proof
  Cases_on `take_call_outcome target calldata value_opt st` >>
  rename1 `take_call_outcome target calldata value_opt st = (res,st')` >>
  Cases_on `res` >> simp[] >> drule take_call_outcome_error >> rw[]
QED

Theorem take_call_outcome_success:
  take_call_outcome target calldata value_opt st = (INL (rq,outcome), st') ==>
  ?os rest.
    st.outcomes = SOME os /\
    rq = call_outcome_request target calldata value_opt st /\
    take_outcome rq os = (outcome,rest) /\
    st' = st with <|outcomes := SOME rest;
                   requests := record_request rq st.requests|> /\
    (outcome.co_success /\ ~rq.cr_static ==>
       accounts_runtime_well_typed outcome.co_accounts)
Proof
  Cases_on `st.outcomes` >> simp[take_call_outcome_def] >>
  pairarg_tac >> rw[] >> gvs[]
QED

Theorem take_call_outcome_suffix:
  take_call_outcome target calldata value_opt st = (res,st') /\
  st.outcomes = SOME os ==>
  ?rest prefix. st'.outcomes = SOME rest /\ os = prefix ++ rest /\
    LENGTH prefix <= 1 /\
    (computed_precompile (call_outcome_request target calldata value_opt st) ==>
       prefix = [] /\ st'.requests = st.requests)
Proof
  rpt strip_tac >> gvs[take_call_outcome_def] >> pairarg_tac >>
  gvs[AllCaseEqs(), take_outcome_def, record_request_def] >>
  TRY (qexists_tac `[]` >> simp[] >> NO_TAC) >>
  rename1 `os = head::tail` >> qexists_tac `[head]` >> simp[]
QED

Theorem take_adopt_call_outcome_typed:
  accounts_runtime_well_typed st.accounts /\
  take_call_outcome target calldata value_opt st = (INL (rq,outcome),st') /\
  adopt_call_outcome rq outcome st' = (INL (),st'') ==>
  accounts_runtime_well_typed st''.accounts
Proof
  rpt strip_tac >> drule take_call_outcome_success >> strip_tac >>
  Cases_on `rq.cr_static` >> Cases_on `outcome.co_success` >>
  gvs[adopt_call_outcome_equation, call_outcome_request_def]
QED
