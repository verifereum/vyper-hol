signature vyperTestRunnerLib = sig

  val all_traces : string -> Term.term list
  val trace_chunk : int * int -> Term.term list -> Term.term list
  val run_tests_on_traces : Term.term list -> unit

end
