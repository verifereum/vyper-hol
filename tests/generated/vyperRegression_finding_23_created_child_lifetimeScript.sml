Theory vyperRegression_finding_23_created_child_lifetime[no_sig_docs]
Ancestors
  vyperRegressionDefs_finding_23_created_child_lifetime vyperRegressionState
Libs cv_transLib wordsLib

val () = let
  val th = cv_eval ``
    regression_account_empty 0x1076676756f7b54fdedabf0c24eaec735af6ad6bw
      (run_regression_traces
        traces_regression_finding_23_created_child_lifetime_0)``
in
  if aconv (rhs (concl th)) ``T`` then ()
  else raise Fail "finding 23: same-transaction destroyed child remains present"
end;
