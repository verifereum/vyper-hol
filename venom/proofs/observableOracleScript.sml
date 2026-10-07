(* Successful observable requests, with intentional oracle/failure freedom.
 * Exact seven-field observability; no leftover-outcomes requirement. *)
Theory observableOracle
Ancestors
  stateEquiv stateEquivProps venomState venomExecSemantics

Theorem observable_equiv_requests:
  observable_equiv s1 s2 ==> s1.vs_requests = s2.vs_requests
Proof
  simp[observable_equiv_def]
QED

Theorem observable_equiv_oracle_updates:
  observable_equiv
    (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  observable_equiv
    (s1 with vs_requests := rqs2) (s2 with vs_requests := rqs2) /\
  rqs1 = rqs2
Proof
  simp[observable_equiv_def] >> metis_tac[]
QED

Theorem observable_equiv_same_requests:
  observable_equiv s1 s2 ==>
  observable_equiv
    (s1 with <| vs_outcomes := os1; vs_requests := rqs |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs |>)
Proof
  simp[observable_equiv_def]
QED

Theorem observable_equiv_outcome_freedom:
  observable_equiv (s1 with vs_outcomes := os1)
    (s2 with vs_outcomes := os2) <=> observable_equiv s1 s2
Proof
  simp[observable_equiv_def]
QED

Theorem revert_equiv_oracle_freedom:
  revert_equiv
    (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>)
    (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>) <=>
  revert_equiv s1 s2
Proof
  simp[revert_equiv_def]
QED

(* Success constructors retain exactly their old state/value comparisons
 * and now expose requests. Abort and Error remain request-free. *)
Theorem observable_result_requests:
  (observable_result_equiv (OK s1) (OK s2) ==>
    s1.vs_requests = s2.vs_requests) /\
  (observable_result_equiv (Halt s1) (Halt s2) ==>
    s1.vs_requests = s2.vs_requests) /\
  (observable_result_equiv (IntRet v1 s1) (IntRet v2 s2) ==>
    s1.vs_requests = s2.vs_requests /\ v1 = v2)
Proof
  simp[observable_result_equiv_def, observable_equiv_def]
QED

Theorem observable_abort_oracle_freedom:
  observable_result_equiv
    (Abort a1 (s1 with <| vs_outcomes := os1; vs_requests := rqs1 |>))
    (Abort a2 (s2 with <| vs_outcomes := os2; vs_requests := rqs2 |>)) <=>
  a1 = a2 /\ revert_equiv s1 s2
Proof
  simp[observable_result_equiv_def, revert_equiv_def]
QED

(* Nonempty witnesses separate outcome freedom and successful request checking.
 * No default init state is used. *)
Theorem observable_outcome_counterexample:
  observable_equiv (s with vs_outcomes := [])
    (s with vs_outcomes := [outcome]) /\
  (s with vs_outcomes := []).vs_outcomes <>
    (s with vs_outcomes := [outcome]).vs_outcomes
Proof
  simp[observable_equiv_def]
QED

Theorem observable_request_counterexample:
  ~observable_equiv (s with vs_requests := [])
    (s with vs_requests := [request]) /\
  observable_result_equiv (Abort a (s with vs_requests := []))
    (Abort a (s with vs_requests := [request])) /\
  observable_result_equiv (Error e1) (Error e2)
Proof
  simp[observable_equiv_def, observable_result_equiv_def, revert_equiv_def]
QED
