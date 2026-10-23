(* Source oracle boundary, deliberately below vyperInterpreter.
 * TOP-LEVEL: call_outcome_request, take_call_outcome, adopt_call_outcome.
 * The evaluator owns the successful nonstatic account check; the oracle has
 * no typing premise. Adoption is raw: its actual client first takes/checks.
 * No live evaluator clause is changed by this theory.
 *)
Theory vyperCallOutcome
Ancestors
  arithmetic list option pair sum
  extCallOracle vyperState vyperValue vyperRuntimeAccounts
Libs cv_transLib

Definition call_outcome_request_def:
  call_outcome_request target calldata value_opt st =
    <| cr_kind := MessageCall; cr_gas := NONE; cr_data_len := LENGTH calldata;
       cr_target := target;
       cr_value := (case value_opt of NONE => 0 | SOME v => v);
       cr_data := calldata;
       cr_static := IS_NONE value_opt;
       cr_accounts := st.accounts;
       cr_tStorage := st.tStorage |>
End
val () = cv_auto_trans call_outcome_request_def;

Definition take_call_outcome_def:
  take_call_outcome target calldata value_opt st =
    case st.outcomes of
      NONE => (INR (Error (RuntimeError "take_call_outcome")), st)
    | SOME os =>
      let rq = call_outcome_request target calldata value_opt st in
      let (outcome, rest) = take_outcome rq os in
      let st' = st with <| outcomes := SOME rest;
                          requests := record_request rq st.requests |> in
      if outcome.co_success /\ ~rq.cr_static /\
         ~accounts_runtime_well_typed outcome.co_accounts
      then (INR (Error (RuntimeError "call outcome accounts")), st')
      else (INL (rq, outcome), st')
End
val () = take_call_outcome_def |> SRULE [pairTheory.pair_CASE_def] |> cv_auto_trans;

Definition adopt_call_outcome_def:
  adopt_call_outcome rq outcome st =
    let (accounts, tStorage, logs) =
      adopt_outcome rq outcome (st.accounts, st.tStorage, st.logs) in
    return () (st with <| accounts := accounts; tStorage := tStorage;
                         logs := logs;
                         pending_deletions := if computed_precompile rq then st.pending_deletions
                           else adopt_outcome_deletions rq outcome st.pending_deletions |>)
End
val () = adopt_call_outcome_def |> SRULE [pairTheory.pair_CASE_def] |> cv_auto_trans;

(* ===== Exact equations ===== *)

(* Definitional identity with PLAN 5.3, including the shared live snapshots.
   The request constructor is factored only to avoid repeating that record. *)
Theorem take_call_outcome_plan:
  take_call_outcome target calldata value_opt st =
    case st.outcomes of
      NONE => (INR (Error (RuntimeError "take_call_outcome")),st)
    | SOME os =>
      let rq = <|cr_kind := MessageCall; cr_gas := NONE; cr_data_len := LENGTH calldata;
                 cr_target := target;
                 cr_value := (case value_opt of NONE => 0 | SOME v => v);
                 cr_data := calldata; cr_static := IS_NONE value_opt;
                 cr_accounts := st.accounts; cr_tStorage := st.tStorage|> in
      let (outcome,rest) = take_outcome rq os in
      let st' = st with <|outcomes := SOME rest;
                          requests := record_request rq st.requests|> in
      if outcome.co_success /\ ~rq.cr_static /\
         ~accounts_runtime_well_typed outcome.co_accounts then
        (INR (Error (RuntimeError "call outcome accounts")),st')
      else (INL (rq,outcome),st')
Proof
  simp[take_call_outcome_def, call_outcome_request_def]
QED

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

Theorem adopt_call_outcome_equation:
  adopt_call_outcome rq outcome st =
    (INL (), if rq.cr_static then st else
       if outcome.co_success then
         st with <|accounts := outcome.co_accounts;
                   tStorage := outcome.co_tStorage;
                   logs := st.logs ++ outcome.co_logs;
                   pending_deletions := if computed_precompile rq
                     then st.pending_deletions else outcome.co_toDelete|>
       else if rq.cr_kind = MessageCall then st
       else st with <|accounts := outcome.co_accounts;
                     tStorage := outcome.co_tStorage|>)
Proof
  rw[adopt_call_outcome_def, adopt_outcome_def, adopt_outcome_deletions_def, return_def] >>
  gvs[evaluation_state_component_equality]
QED

(* ===== Whole-record frame and guarded typing ===== *)

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

Theorem take_call_outcome_frame:
  take_call_outcome target calldata value_opt st = (res, st') ==>
  st' = st with <|outcomes := st'.outcomes; requests := st'.requests|>
Proof
  Cases_on `st.outcomes` >>
  simp[take_call_outcome_def] >>
  pairarg_tac >> rw[] >> gvs[]
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

Theorem adopt_call_outcome_frame:
  adopt_call_outcome rq outcome st = (res,st') ==>
  res = INL () /\
  st' = st with <|accounts := st'.accounts; tStorage := st'.tStorage;
                 logs := st'.logs; pending_deletions := st'.pending_deletions|>
Proof
  rw[adopt_call_outcome_equation, adopt_outcome_deletions_def] >>
  gvs[evaluation_state_component_equality]
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

Theorem adopt_call_outcome_computed_deletions:
  computed_precompile rq ==>
  (SND (adopt_call_outcome rq outcome st)).pending_deletions = st.pending_deletions
Proof
  rw[adopt_call_outcome_equation] >> gvs[]
QED

Theorem adopt_call_outcome_observed_deletions:
  ~computed_precompile rq /\ outcome.co_success /\ ~rq.cr_static ==>
  (SND (adopt_call_outcome rq outcome st)).pending_deletions = outcome.co_toDelete
Proof
  rw[adopt_call_outcome_equation] >> gvs[]
QED

Theorem adopt_call_outcome_static_failed_deletions:
  rq.cr_static \/ ~outcome.co_success ==>
  (SND (adopt_call_outcome rq outcome st)).pending_deletions = st.pending_deletions
Proof
  rw[adopt_call_outcome_equation] >> gvs[]
QED

(* Nonempty queues detect synthetic precompile snapshots being mistaken
   for an observed empty snapshot. No precompile algorithm is unfolded. *)
Theorem computed_success_keeps_pending_regression:
  rq.cr_kind = MessageCall /\ rq.cr_value = 0 /\ rq.cr_target = 1w /\ rq.cr_data = [] ==>
  (SND (adopt_call_outcome rq (FST (take_outcome rq os))
    (st with pending_deletions := [9w]))).pending_deletions = [9w]
Proof
  strip_tac >>
  `computed_precompile rq` by
    simp[computed_precompile_def, precompile_result_empty_ecrecover] >>
  simp[adopt_call_outcome_computed_deletions]
QED

Theorem observed_success_replaces_pending_regression:
  ~computed_precompile rq /\ ~rq.cr_static ==>
  (SND (adopt_call_outcome rq (outcome with <|co_success := T; co_toDelete := []|>)
    (st with pending_deletions := [9w]))).pending_deletions = [] /\
  (SND (adopt_call_outcome rq (outcome with <|co_success := T; co_toDelete := [8w]|>)
    (st with pending_deletions := [9w]))).pending_deletions = [8w]
Proof
  strip_tac >> simp[adopt_call_outcome_observed_deletions]
QED
