open HolKernel vyperTestRunnerLib vyperTestDefs60Theory;
val () = new_theory "vyperTest60";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs60";
val () = export_theory_no_docs();
