open HolKernel vyperTestRunnerLib vyperTestDefs66Theory;
val () = new_theory "vyperTest66";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs66";
val () = export_theory_no_docs();
