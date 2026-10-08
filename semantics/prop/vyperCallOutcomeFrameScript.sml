(* Oracle tail property transport. Whole-record facts supply the boundary;
 * R can be a residual frame, scope/type-value frame, or log-prefix relation.
 * No purity/storage claim about external payloads and no typing premise on os.
 * This owner remains below Interpreter and TypeSystem.
 *)
Theory vyperCallOutcomeFrame
Ancestors
  pair sum list option vyperState vyperCallOutcome vyperCallOutcomeBranches
  vyperRuntimeAccounts extCallOracle
Libs monadsyntax

(* Keep underconstrained client monads in the source state/exception type. *)
val () = monadsyntax.enable_monad "vyper_evaluation";
val () = Parse.type_abbrev ("exception", ``:vyperState$exception``);
val _ = hide "body";

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
  (!s accounts transient logs.
    R s (s with <|accounts := accounts; tStorage := transient;
                  logs := s.logs ++ logs|>)) /\
  adopt_call_outcome rq outcome st = (res,st') ==>
  R st st'
Proof
  rw[adopt_call_outcome_equation] >> gvs[]
QED

Theorem checked_call_outcome_transport:
  (!s. R s s) /\
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!s os rqs. R s (s with <|outcomes := os; requests := rqs|>)) /\
  (!s accounts transient logs.
    R s (s with <|accounts := accounts; tStorage := transient;
                  logs := s.logs ++ logs|>)) /\
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
Theorem ExtCall_outcome_checked_tail[local]:
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
  Cases_on `take_call_outcome target calldata value_opt st` >>
  rename1 `take_call_outcome target calldata value_opt st = (answer,mid)` >>
  drule ExtCall_outcome_continue >>
  disch_then (qspecl_then [`ret_type`,`k`] mp_tac) >>
  drule checked_call_outcome_continue >>
  disch_then (qspecl_then [`"ExtCall reverted"`,`k`] mp_tac) >>
  rpt strip_tac >> asm_rewrite_tac[]
QED

Theorem ExtCall_outcome_transport:
  (!s. R s s) /\
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!s os rqs. R s (s with <|outcomes := os; requests := rqs|>)) /\
  (!s accounts transient logs.
    R s (s with <|accounts := accounts; tStorage := transient;
                  logs := s.logs ++ logs|>)) /\
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
  (!s accounts transient logs.
    R s (s with <|accounts := accounts; tStorage := transient;
                  logs := s.logs ++ logs|>)) /\
  (do
    (rq,outcome) <- take_call_outcome target [] (SOME amount);
    check outcome.co_success "send failed";
    adopt_call_outcome rq outcome;
    return (Value NoneV)
  od) st = (res,st') ==>
  R st st'
Proof
  rpt strip_tac >>
  irule (checked_call_outcome_transport |> INST_TYPE [alpha |-> ``:toplevel_value``]) >>
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
                   logs := st2.logs|> /\
    (outcome.co_success /\ ~rq.cr_static ==>
      st2.accounts = outcome.co_accounts /\
      st2.tStorage = outcome.co_tStorage /\
      st2.logs = st.logs ++ outcome.co_logs /\
      accounts_runtime_well_typed st2.accounts) /\
    (rq.cr_static \/ ~outcome.co_success ==>
      st2.accounts = st.accounts /\ st2.tStorage = st.tStorage /\
      st2.logs = st.logs) /\
    (computed_precompile rq ==> prefix = [] /\ st2.requests = st.requests)
Proof
  rpt strip_tac >> drule_all checked_call_outcome_success_frame >> strip_tac >>
  drule take_call_outcome_success >> strip_tac >>
  drule_all take_call_outcome_suffix >> strip_tac >>
  gvs[adopt_call_outcome_equation] >>
  qexistsl_tac [`rest`,`prefix`] >>
  IF_CASES_TAC >> gvs[evaluation_state_component_equality]
QED
