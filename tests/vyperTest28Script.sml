open HolKernel vyperTestRunnerLib vyperTestDefs28Theory;
val () = new_theory "vyperTest28";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs28";
val () = export_theory_no_docs();
