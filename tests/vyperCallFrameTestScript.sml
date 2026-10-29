(* Focused checks of call frames and expanded pure-state equality. *)
Theory vyperCallFrameTest
Ancestors
  list option pair sum finite_map
  vyperAST vyperValue vyperState vyperInterpreter vyperStatePreservation
  vyperCallOutcome vyperCallOutcomeBranches vyperCallFrame vyperCallOutcomeFrame
  vyperRuntimeAccounts vyperPureExpr vyperCallOutcomeTest
  vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes
  vyperEvalPreservesImmutablesDom vyperLogPreservation
  vyperTypeEnvPreservation
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val _ = hide "body";

Theorem extcall_code_failure_precedes_take:
  NULL (lookup_account target st.accounts).code ==>
  (do
    accounts <- get_accounts;
    (if NoneT = NoneT then
       check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success "ExtCall reverted";
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = (INR (Error (RuntimeError "ExtCall target has no code")),st)
Proof
  strip_tac >>
  simp[bind_def, ignore_bind_def, get_accounts_def, return_def,
       check_def, assert_def, raise_def]
QED

Theorem send_failure_keeps_taken_state:
  take_call_outcome target [] (SOME amount) st = (INL (rq,outcome),st1) /\
  ~outcome.co_success ==>
  (do
    (rq,outcome) <- take_call_outcome target [] (SOME amount);
    check outcome.co_success "send failed";
    adopt_call_outcome rq outcome;
    return (Value NoneV)
  od) st = (INR (Error (RuntimeError "send failed")),st1)
Proof
  rpt strip_tac >> drule Send_outcome_continue >> simp[]
QED

Theorem checked_tail_has_only_its_runtime_errors:
  accounts_runtime_well_typed st.accounts /\
  (!bs s exc t. k bs s <> (INR exc,t)) /\
  (do
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success msg;
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = (INR exc,st') ==> ?text. exc = Error (RuntimeError text)
Proof
  rpt strip_tac >> drule_all checked_call_outcome_exception >>
  strip_tac >> metis_tac[]
QED

(* Actual successful take discharges the payload account guard; no hypothesis
   asserts that an arbitrary future os is typed. This also rejects call purity. *)
Theorem successful_adoption_can_change_accounts:
  take_call_outcome target calldata value_opt st = (INL (rq,outcome),st1) /\
  adopt_call_outcome rq outcome st1 = (INL (),st2) /\
  outcome.co_success /\ ~rq.cr_static /\ outcome.co_accounts <> st.accounts ==>
  accounts_runtime_well_typed st2.accounts /\ st2 <> st
Proof
  rpt strip_tac >> drule_all take_adopt_call_outcome_effects >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem static_adoption_does_not_install_payload:
  take_call_outcome target calldata value_opt st = (INL (rq,outcome),st1) /\
  adopt_call_outcome rq outcome st1 = (INL (),st2) /\ rq.cr_static ==>
  st2.accounts = st.accounts /\ st2.tStorage = st.tStorage /\ st2.logs = st.logs
Proof
  rpt strip_tac >> drule_all take_adopt_call_outcome_effects >> strip_tac >> gvs[]
QED

(* The exact executable decoder continuation, not a replacement decoder. *)
Theorem extcall_decode_continuation_state:
  (do
    v <- lift_sum_runtime (evaluate_abi_decode_return tenv ret_type bs);
    return (Value v)
  od) st = (res,st') ==> st' = st
Proof
  simp[bind_def, return_def] >>
  Cases_on `lift_sum_runtime (evaluate_abi_decode_return tenv ret_type bs) st` >>
  rename1 `lift_sum_runtime _ st = (answer,mid)` >>
  Cases_on `answer` >> simp[] >> strip_tac >> gvs[] >>
  drule lift_sum_runtime_state >> simp[]
QED

(* Equality includes control, storage, logs, and both newly expanded fields.
   outcomes is arbitrary: NONE, SOME [], and populated SOME all satisfy it. *)
Theorem pure_expression_expanded_state:
  pure_expr e /\ eval_expr cx e st = (res,st') ==>
  st' = st /\ st'.outcomes = st.outcomes /\ st'.requests = st.requests /\
  st'.accounts = st.accounts /\ st'.tStorage = st.tStorage /\
  st'.logs = st.logs /\ st'.scopes = st.scopes /\ st'.immutables = st.immutables
Proof
  rpt strip_tac >> drule_all eval_expr_preserves_state >> simp[]
QED

Theorem pure_expression_list_expanded_state:
  EVERY pure_expr es /\ eval_exprs cx es st = (res,st') ==>
  st' = st /\ st'.outcomes = st.outcomes /\ st'.requests = st.requests
Proof
  rpt strip_tac >> drule_all eval_exprs_preserves_state >> simp[]
QED
