Theory vyperRegression_finding_43_nested_creation_deletion[no_sig_docs]
Ancestors
  vyperRegressionDefs_finding_43_nested_creation_deletion vyperRegressionState
Libs cv_transLib wordsLib

val () = let
  val th = cv_eval ``
    regression_account_empty 0x1076676756f7b54fdedabf0c24eaec735af6ad6bw
      (run_regression_traces
        traces_regression_finding_43_nested_creation_deletion_0)``
in
  if aconv (rhs (concl th)) ``T`` then ()
  else raise Fail "finding 43: nested-call destroyed child remains present"
end;
