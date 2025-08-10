open HolKernel vyperTestRunnerLib vyperTestDefs76Theory;
val () = new_theory "vyperTest76";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs76";
val () = export_theory_no_docs();
