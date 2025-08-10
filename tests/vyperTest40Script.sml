open HolKernel vyperTestRunnerLib vyperTestDefs40Theory;
val () = new_theory "vyperTest40";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs40";
val () = export_theory_no_docs();
