open HolKernel vyperTestRunnerLib vyperTestDefs02Theory;
val () = new_theory "vyperTest02";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs02";
val () = export_theory_no_docs();
