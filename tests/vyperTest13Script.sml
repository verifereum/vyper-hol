open HolKernel vyperTestRunnerLib vyperTestDefs13Theory;
val () = new_theory "vyperTest13";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs13";
val () = export_theory_no_docs();
