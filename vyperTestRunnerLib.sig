signature vyperTestRunnerLib = sig

  val all_traces : string -> Term.term list
  val run_test_on_traces : Term.term -> unit

end
