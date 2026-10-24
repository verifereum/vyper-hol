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
    <| cr_target := target;
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
                         logs := logs |>)
End
val () = adopt_call_outcome_def |> SRULE [pairTheory.pair_CASE_def] |> cv_auto_trans;
