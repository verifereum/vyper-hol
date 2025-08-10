open HolKernel vyperTestRunnerLib vyperTestDefs84Theory;
val () = new_theory "vyperTest84";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs84";
val () = export_theory_no_docs();
