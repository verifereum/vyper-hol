open HolKernel vyperTestRunnerLib vyperTestDefs12Theory;
val () = new_theory "vyperTest12";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs12";
val () = export_theory_no_docs();
