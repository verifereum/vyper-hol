open HolKernel vyperTestRunnerLib vyperTestDefs48Theory;
val () = new_theory "vyperTest48";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs48";
val () = export_theory_no_docs();
