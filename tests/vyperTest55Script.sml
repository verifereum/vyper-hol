open HolKernel vyperTestRunnerLib vyperTestDefs55Theory;
val () = new_theory "vyperTest55";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs55";
val () = export_theory_no_docs();
