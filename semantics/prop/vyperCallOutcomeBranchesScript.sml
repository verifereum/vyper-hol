(* Parameterized post-calldata branch contracts. No second evaluator and no
 * live activation: k is exactly the default/decode/return continuation chosen
 * by the evaluator. These equations also serve CPS clients.
 * This owner, like the definitions, can be an Interpreter/SmallStep parent.
 *)
Theory vyperCallOutcomeBranches
Ancestors
  list option pair sum vyperAST vyperValue vyperState vyperCallOutcome vyperCallOutcomeProps
  vyperRuntimeAccounts extCallOracle vfmState
Libs monadsyntax

(* ===== Shared checked continuation ===== *)

Theorem checked_call_outcome_continue:
  take_call_outcome target calldata value_opt st = (res,st1) ==>
  (do
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success msg;
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st =
  case res of
    INR exc => (INR exc,st1)
  | INL (rq,outcome) =>
      if outcome.co_success then
        k outcome.co_returnData (SND (adopt_call_outcome rq outcome st1))
      else (INR (Error (RuntimeError msg)),st1)
Proof
  strip_tac >> simp[bind_def, ignore_bind_def, check_def, assert_def] >>
  Cases_on `res` >- (rename1 `INL ro` >> Cases_on `ro` >>
    simp[adopt_call_outcome_equation, bind_def, ignore_bind_def, assert_def] >>
    rw[] >> gvs[]) >> simp[]
QED

(* A decomposition usable for arbitrary frame, typing, storage, or control
   postconditions: the recursive continuation is never unfolded. *)
Theorem checked_call_outcome_cases:
  (do
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success msg;
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = result <=>
  (?exc st1. take_call_outcome target calldata value_opt st = (INR exc,st1) /\
             result = (INR exc,st1)) \/
  (?rq outcome st1.
    take_call_outcome target calldata value_opt st = (INL (rq,outcome),st1) /\
    ~outcome.co_success /\ result = (INR (Error (RuntimeError msg)),st1)) \/
  (?rq outcome st1 st2.
    take_call_outcome target calldata value_opt st = (INL (rq,outcome),st1) /\
    outcome.co_success /\ adopt_call_outcome rq outcome st1 = (INL (),st2) /\
    k outcome.co_returnData st2 = result)
Proof
  Cases_on `take_call_outcome target calldata value_opt st` >>
  rename1 `take_call_outcome target calldata value_opt st = (res,st1)` >>
  drule checked_call_outcome_continue >> disch_then (qspecl_then [`msg`,`k`] mp_tac) >>
  Cases_on `res` >- (rename1 `INL ro` >> Cases_on `ro` >>
    simp[adopt_call_outcome_equation] >> rw[] >> gvs[EQ_SYM_EQ]) >>
  simp[EQ_SYM_EQ]
QED

(* The only newly generated exceptions are runtime errors. Any other error
   must come from k, so no-TypeError/control proofs stay at the parameterized
   interface. st2's accounts are typed by the evaluator's guard. *)
Theorem checked_call_outcome_exception:
  accounts_runtime_well_typed st.accounts /\
  (do
    (rq,outcome) <- take_call_outcome target calldata value_opt;
    check outcome.co_success msg;
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = (INR exc,st') ==>
  (?s. exc = Error (RuntimeError s)) \/
  (?bs st2. accounts_runtime_well_typed st2.accounts /\
            k bs st2 = (INR exc,st'))
Proof
  simp[checked_call_outcome_cases] >> rpt strip_tac
  >- (drule take_call_outcome_error >> rw[] >> simp[])
  >- simp[] >>
  disj2_tac >> qexistsl_tac [`outcome.co_returnData`,`st2`] >> simp[] >>
  drule_all take_adopt_call_outcome_typed >> simp[]
QED

(* ===== ExtCall and Send exact branch rules ===== *)

Theorem Send_outcome_continue:
  take_call_outcome target [] (SOME amount) st = (res,st1) ==>
  (do
    (rq,outcome) <- take_call_outcome target [] (SOME amount);
    check outcome.co_success "send failed";
    adopt_call_outcome rq outcome;
    return (Value NoneV)
  od) st =
    case res of
      INR exc => (INR exc,st1)
    | INL (rq,outcome) =>
        if outcome.co_success then
          (INL (Value NoneV),SND (adopt_call_outcome rq outcome st1))
        else (INR (Error (RuntimeError "send failed")),st1)
Proof
  strip_tac >> simp[bind_def, ignore_bind_def, check_def, assert_def] >>
  Cases_on `res` >- (rename1 `INL ro` >> Cases_on `ro` >>
    simp[adopt_call_outcome_equation, bind_def, ignore_bind_def,
         assert_def, vyperStateTheory.return_def] >> rw[] >> gvs[]) >> simp[]
QED

(* Real request snapshots, not an unconstrained rq: at the continuation entry
   the residual frame is unchanged outside the observable/oracle fields.
   This intentionally does not assert arbitrary adopted storage is preserved. *)
Theorem checked_call_outcome_success_frame:
  take_call_outcome target calldata value_opt st = (INL (rq,outcome),st1) /\
  adopt_call_outcome rq outcome st1 = (INL (),st2) ==>
  rq.cr_accounts = st.accounts /\ rq.cr_tStorage = st.tStorage /\
  st2 = st with <|accounts := st2.accounts; tStorage := st2.tStorage;
                 logs := st2.logs; outcomes := st2.outcomes;
                 requests := st2.requests;
                 pending_deletions := st2.pending_deletions|>
Proof
  rpt strip_tac >> drule take_call_outcome_success >> strip_tac >>
  gvs[call_outcome_request_def, adopt_call_outcome_equation] >>
  IF_CASES_TAC >> simp[evaluation_state_component_equality]
QED
