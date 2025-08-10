open HolKernel vyperTestRunnerLib vyperTestDefs35Theory;
val () = new_theory "vyperTest35";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs35";
val () = export_theory_no_docs();
