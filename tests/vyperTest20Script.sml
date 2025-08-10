open HolKernel vyperTestRunnerLib vyperTestDefs20Theory;
val () = new_theory "vyperTest20";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs20";
val () = export_theory_no_docs();
