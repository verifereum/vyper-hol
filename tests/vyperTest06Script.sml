open HolKernel vyperTestRunnerLib vyperTestDefs06Theory;
val () = new_theory "vyperTest06";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs06";
val () = export_theory_no_docs();
