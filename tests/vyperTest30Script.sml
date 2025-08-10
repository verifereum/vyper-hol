open HolKernel vyperTestRunnerLib vyperTestDefs30Theory;
val () = new_theory "vyperTest30";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs30";
val () = export_theory_no_docs();
