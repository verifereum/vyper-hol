open HolKernel vyperTestRunnerLib vyperTestDefs47Theory;
val () = new_theory "vyperTest47";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs47";
val () = export_theory_no_docs();
