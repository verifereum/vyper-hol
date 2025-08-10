open HolKernel vyperTestRunnerLib vyperTestDefs61Theory;
val () = new_theory "vyperTest61";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs61";
val () = export_theory_no_docs();
