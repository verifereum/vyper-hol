open HolKernel vyperTestRunnerLib vyperTestDefs10Theory;
val () = new_theory "vyperTest10";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs10";
val () = export_theory_no_docs();
