Theory vyperRegression_finding_50_constructor_selfdestruct[no_sig_docs]
Ancestors
  vyperRegressionDefs_finding_50_constructor_selfdestruct vyperRegressionState
Libs cv_transLib wordsLib

val () = let
  val th = cv_eval ``
    regression_account_empty 0xed4efeaed8057c619a6d7aacc0459874eaf3c166w
      (run_regression_traces
        traces_regression_finding_50_constructor_selfdestruct_0)``
in
  if aconv (rhs (concl th)) ``T`` then ()
  else raise Fail "finding 50: selfdestructed constructor account remains present"
end;
