open HolKernel vyperTestRunnerLib vyperTestDefs86Theory;
val () = new_theory "vyperTest86";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs86";
val () = export_theory_no_docs();
