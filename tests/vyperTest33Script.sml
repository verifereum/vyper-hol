open HolKernel vyperTestRunnerLib vyperTestDefs33Theory;
val () = new_theory "vyperTest33";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs33";
val () = export_theory_no_docs();
