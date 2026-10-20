Theory vyperRegression_finding_03_indexed_bytes20_topic[no_sig_docs]
Ancestors
  vyperRegressionDefs_finding_03_indexed_bytes20_topic vyperRegressionState
Libs cv_transLib wordsLib

val () = let
  val th = cv_eval ``
    regression_first_log_topics
      (run_regression_traces
        traces_regression_finding_03_indexed_bytes20_topic_0) =
    SOME [0xc24508c989449ac13ef418e13692063a60e4b70a2ff8591d4421ae9064d5d0c1;
          0x1111111111111111111111111111111111111111000000000000000000000000]``
in
  if aconv (rhs (concl th)) ``T`` then ()
  else raise Fail "finding 03: indexed bytes20 event topic is not right-padded"
end;
