Theory vyperRegressionState
Ancestors
  vyperTestRunner
Libs
  cv_transLib

Definition run_regression_trace_def:
  run_regression_trace NONE trace = NONE ∧
  run_regression_trace (SOME (snss,am)) trace =
    case run_trace snss am trace of
    | (snss', INL am') => SOME (snss',am')
    | (_, INR _) => NONE
End

val () = cv_auto_trans run_regression_trace_def;

Definition run_regression_traces_def:
  run_regression_traces traces =
    OPTION_MAP SND
      (FOLDL run_regression_trace (SOME ([],initial_machine_state)) traces)
End


Definition regression_first_log_topics_def:
  regression_first_log_topics NONE = NONE ∧
  regression_first_log_topics (SOME (am:abstract_machine)) =
    case am.logs of [] => NONE | ev::_ => SOME (MAP w2n ev.topics)
End

val () = cv_auto_trans regression_first_log_topics_def;

Definition regression_account_empty_def:
  regression_account_empty (address:address) NONE = F ∧
  regression_account_empty address (SOME (am:abstract_machine)) =
    (lookup_account address am.accounts = empty_account_state)
End

val () = cv_auto_trans regression_account_empty_def;
val () = cv_auto_trans run_regression_traces_def;
