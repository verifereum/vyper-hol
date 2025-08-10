open HolKernel vyperTestRunnerLib vyperTestDefs57Theory;
val () = new_theory "vyperTest57";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs57";
val () = export_theory_no_docs();
