open HolKernel vyperTestRunnerLib vyperTestDefs53Theory;
val () = new_theory "vyperTest53";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs53";
val () = export_theory_no_docs();
