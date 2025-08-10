open HolKernel vyperTestRunnerLib vyperTestDefs36Theory;
val () = new_theory "vyperTest36";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs36";
val () = export_theory_no_docs();
