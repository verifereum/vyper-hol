Theory vyperRegression_finding_21_event_argument_order[no_sig_docs]
Ancestors
  vyperRegressionDefs_finding_21_event_argument_order vyperRegressionState
Libs cv_transLib wordsLib

val () = let
  val th = cv_eval ``
    regression_first_log_topics
      (run_regression_traces
        traces_regression_finding_21_event_argument_order_0) =
    SOME [0x34d9e1bdb1ad30041a1a7461dfe6258ddbe9035290cd4c7333cc90ad33ad09c9;
          1]``
in
  if aconv (rhs (concl th)) ``T`` then ()
  else raise Fail "finding 21: legacy event arguments are evaluated in the wrong order"
end;
