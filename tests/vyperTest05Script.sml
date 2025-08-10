open HolKernel vyperTestRunnerLib vyperTestDefs05Theory;
val () = new_theory "vyperTest05";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs05";
val () = export_theory_no_docs();
