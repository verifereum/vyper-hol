open HolKernel vyperTestRunnerLib vyperTestDefs85Theory;
val () = new_theory "vyperTest85";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs85";
val () = export_theory_no_docs();
