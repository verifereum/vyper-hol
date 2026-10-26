(* Source oracle boundary, deliberately below vyperInterpreter.
 * TOP-LEVEL: call_outcome_request, create_outcome_request,
 * take_call_outcome, take_create_outcome, adopt_call_outcome.
 * Taking validates adopted accounts; CREATE validates failures too, since
 * they retain nonce changes. Adoption is raw: clients first take/check.
 * Call equations and guarded typing facts live in vyperCallOutcomeProps.
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

(* The evaluator's frame proofs use these. *)

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

Theorem take_call_outcome_frame:
  take_call_outcome target calldata value_opt st = (res, st') ==>
  st' = st with <|outcomes := st'.outcomes; requests := st'.requests|>
Proof
  Cases_on `st.outcomes` >>
  simp[take_call_outcome_def] >>
  pairarg_tac >> rw[] >> gvs[]
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

Theorem adopt_call_outcome_frame:
  adopt_call_outcome rq outcome st = (res,st') ==>
  res = INL () /\
  st' = st with <|accounts := st'.accounts; tStorage := st'.tStorage;
                 logs := st'.logs; pending_deletions := st'.pending_deletions|>
Proof
  rw[adopt_call_outcome_equation, adopt_outcome_deletions_def] >>
  gvs[evaluation_state_component_equality]
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

(* CREATE uses the ordinary outcome stream, never computed precompiles.
   Its account guard also covers failure: the creator nonce is retained. *)
Definition create_outcome_request_def:
  create_outcome_request kind value initcode st =
    <| cr_kind := kind; cr_gas := NONE; cr_data_len := LENGTH initcode;
       cr_target := 0w; cr_value := value; cr_data := initcode;
       cr_static := F; cr_accounts := st.accounts;
       cr_tStorage := st.tStorage |>
End
val () = cv_auto_trans create_outcome_request_def;

Definition take_create_outcome_def:
  take_create_outcome kind value initcode st =
    case st.outcomes of
      NONE => (INR (Error (RuntimeError "take_create_outcome")), st)
    | SOME os =>
      let rq = create_outcome_request kind value initcode st in
      let (outcome, rest) = take_outcome rq os in
      let st' = st with <|outcomes := SOME rest;
                         requests := record_request rq st.requests|> in
      if ~accounts_runtime_well_typed outcome.co_accounts
      then (INR (Error (RuntimeError "create outcome accounts")), st')
      else (INL (rq, outcome), st')
End
val () = take_create_outcome_def |> SRULE [pairTheory.pair_CASE_def] |> cv_auto_trans;

Theorem create_outcome_request_not_computed[simp]:
  ~computed_precompile (create_outcome_request kind value initcode st)
Proof
  simp[computed_precompile_addresses, create_outcome_request_def] >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem take_create_outcome_NONE:
  st.outcomes = NONE ==>
  take_create_outcome kind value initcode st =
    (INR (Error (RuntimeError "take_create_outcome")), st)
Proof
  simp[take_create_outcome_def]
QED

Theorem take_create_outcome_SOME:
  st.outcomes = SOME os /\
  rq = create_outcome_request kind value initcode st /\
  take_outcome rq os = (outcome,rest) ==>
  take_create_outcome kind value initcode st =
    (if ~accounts_runtime_well_typed outcome.co_accounts
     then INR (Error (RuntimeError "create outcome accounts"))
     else INL (rq,outcome),
     st with <|outcomes := SOME rest; requests := st.requests ++ [rq]|>)
Proof
  rpt strip_tac >> gvs[take_create_outcome_def, record_request_def] >>
  rw[] >> gvs[]
QED

Theorem take_create_outcome_ordinary:
  st.outcomes = SOME (outcome::rest) /\
  rq = create_outcome_request kind value initcode st ==>
  take_create_outcome kind value initcode st =
    (if ~accounts_runtime_well_typed outcome.co_accounts
     then INR (Error (RuntimeError "create outcome accounts"))
     else INL (rq,outcome),
     st with <|outcomes := SOME rest; requests := st.requests ++ [rq]|>)
Proof
  rpt strip_tac >> gvs[take_create_outcome_def, take_outcome_def, record_request_def] >>
  rw[] >> gvs[]
QED

Theorem take_create_outcome_exhausted:
  st.outcomes = SOME [] /\
  rq = create_outcome_request kind value initcode st ==>
  take_create_outcome kind value initcode st =
    (if ~accounts_runtime_well_typed st.accounts
     then INR (Error (RuntimeError "create outcome accounts"))
     else INL (rq,failed_outcome rq),
     st with <|outcomes := SOME []; requests := st.requests ++ [rq]|>)
Proof
  rpt strip_tac >>
  `take_outcome rq [] = (failed_outcome rq,[])` by
    simp[take_outcome_def] >>
  drule_all take_create_outcome_SOME >>
  simp[failed_outcome_def, create_outcome_request_def]
QED

Theorem take_create_outcome_guard_rejected:
  st.outcomes = SOME os /\
  rq = create_outcome_request kind value initcode st /\
  take_outcome rq os = (outcome,rest) /\
  ~accounts_runtime_well_typed outcome.co_accounts ==>
  take_create_outcome kind value initcode st =
    (INR (Error (RuntimeError "create outcome accounts")),
     st with <|outcomes := SOME rest; requests := st.requests ++ [rq]|>)
Proof
  rpt strip_tac >> drule_all take_create_outcome_SOME >> simp[]
QED

Theorem take_create_outcome_frame:
  take_create_outcome kind value initcode st = (res,st') ==>
  st' = st with <|outcomes := st'.outcomes; requests := st'.requests|>
Proof
  Cases_on `st.outcomes` >> simp[take_create_outcome_def] >>
  pairarg_tac >> rw[] >> gvs[]
QED

Theorem take_create_outcome_error:
  take_create_outcome kind value initcode st = (INR exc,st') ==>
  exc = Error (RuntimeError "take_create_outcome") \/
  exc = Error (RuntimeError "create outcome accounts")
Proof
  Cases_on `st.outcomes` >> simp[take_create_outcome_def] >>
  pairarg_tac >> rw[] >> gvs[]
QED

Theorem take_create_outcome_no_type_error_control:
  FST (take_create_outcome kind value initcode st) <> INR (Error (TypeError msg)) /\
  FST (take_create_outcome kind value initcode st) <> INR (AssertException msg) /\
  FST (take_create_outcome kind value initcode st) <> INR BreakException /\
  FST (take_create_outcome kind value initcode st) <> INR ContinueException /\
  FST (take_create_outcome kind value initcode st) <> INR (ReturnException v)
Proof
  Cases_on `take_create_outcome kind value initcode st` >>
  rename1 `take_create_outcome kind value initcode st = (res,st')` >>
  Cases_on `res` >> simp[] >> drule take_create_outcome_error >> rw[]
QED

Theorem take_create_outcome_success:
  take_create_outcome kind value initcode st = (INL (rq,outcome),st') ==>
  ?os rest.
    st.outcomes = SOME os /\
    rq = create_outcome_request kind value initcode st /\
    take_outcome rq os = (outcome,rest) /\
    st' = st with <|outcomes := SOME rest; requests := st.requests ++ [rq]|> /\
    accounts_runtime_well_typed outcome.co_accounts
Proof
  Cases_on `st.outcomes` >> simp[take_create_outcome_def, record_request_def] >>
  pairarg_tac >> rw[] >> gvs[]
QED

Theorem take_create_outcome_suffix:
  take_create_outcome kind value initcode st = (res,st') /\
  st.outcomes = SOME os ==>
  ?rest prefix. st'.outcomes = SOME rest /\ os = prefix ++ rest /\
    LENGTH prefix <= 1 /\
    st'.requests = st.requests ++ [create_outcome_request kind value initcode st]
Proof
  rpt strip_tac >> gvs[take_create_outcome_def] >> pairarg_tac >>
  gvs[AllCaseEqs(), take_outcome_def, record_request_def] >>
  TRY (qexists_tac `[]` >> simp[] >> NO_TAC) >>
  rename1 `os = head::tail` >> qexists_tac `[head]` >> simp[]
QED

Theorem adopt_create_outcome_equation:
  kind <> MessageCall ==>
  adopt_call_outcome (create_outcome_request kind value initcode st0) outcome st =
    (INL (), st with <|accounts := outcome.co_accounts;
                      tStorage := outcome.co_tStorage;
                      logs := if outcome.co_success then st.logs ++ outcome.co_logs else st.logs;
                      pending_deletions := if outcome.co_success then outcome.co_toDelete
                                           else st.pending_deletions|>)
Proof
  rw[adopt_call_outcome_equation, create_outcome_request_def] >>
  gvs[evaluation_state_component_equality]
QED

Theorem take_adopt_create_outcome_typed:
  kind <> MessageCall /\
  take_create_outcome kind value initcode st = (INL (rq,outcome),st') /\
  adopt_call_outcome rq outcome st' = (INL (),st'') ==>
  accounts_runtime_well_typed st''.accounts
Proof
  rpt strip_tac >> drule take_create_outcome_success >> strip_tac >>
  Cases_on `outcome.co_success` >> Cases_on `kind = MessageCall` >>
  gvs[adopt_call_outcome_equation, create_outcome_request_def]
QED

Theorem take_create_outcome_preserves_scopes_immutables:
  take_create_outcome kind value initcode st = (res,st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables
Proof
  strip_tac >> drule take_create_outcome_frame >>
  disch_then SUBST1_TAC >> simp[]
QED

Theorem take_create_outcome_preserves_world:
  take_create_outcome kind value initcode st = (res,st') ==>
  st'.accounts = st.accounts /\ st'.tStorage = st.tStorage /\
  st'.logs = st.logs /\ st'.pending_deletions = st.pending_deletions
Proof
  strip_tac >> drule take_create_outcome_frame >>
  disch_then SUBST1_TAC >> simp[]
QED

Theorem adopt_create_outcome_preserves_scopes_immutables:
  adopt_call_outcome (create_outcome_request kind value initcode st0) outcome st = (res,st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables /\
  st'.outcomes = st.outcomes /\ st'.requests = st.requests
Proof
  strip_tac >> drule adopt_call_outcome_frame >> strip_tac >>
  qpat_x_assum `st' = _` SUBST1_TAC >> simp[]
QED

Theorem adopt_create_outcome_logs:
  (SND (adopt_call_outcome (create_outcome_request kind value initcode st0)
           outcome st)).logs =
  st.logs ++ (if outcome.co_success then outcome.co_logs else [])
Proof
  rw[adopt_call_outcome_equation, create_outcome_request_def]
QED

Theorem adopt_create_outcome_deletions:
  (SND (adopt_call_outcome (create_outcome_request kind value initcode st0)
           outcome st)).pending_deletions =
  if outcome.co_success then outcome.co_toDelete else st.pending_deletions
Proof
  rw[adopt_call_outcome_equation, create_outcome_request_def]
QED

Theorem adopt_create_outcome_accounts:
  kind <> MessageCall ==>
  (SND (adopt_call_outcome (create_outcome_request kind value initcode st0)
           outcome st)).accounts = outcome.co_accounts /\
  (SND (adopt_call_outcome (create_outcome_request kind value initcode st0)
           outcome st)).tStorage = outcome.co_tStorage
Proof
  simp[adopt_create_outcome_equation]
QED

(* Kernel audit of this boundary, including its strict prerequisites. *)
val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles andalso null axioms
     then () else raise Fail ("Incomplete oracle boundary: " ^ name)
  end) (DB.thms "vyperCallOutcome");
