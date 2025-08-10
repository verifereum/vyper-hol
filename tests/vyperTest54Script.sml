open HolKernel vyperTestRunnerLib vyperTestDefs54Theory;
val () = new_theory "vyperTest54";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs54";
val () = export_theory_no_docs();
