open HolKernel vyperTestRunnerLib vyperTestDefs24Theory;
val () = new_theory "vyperTest24";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs24";
val () = export_theory_no_docs();
