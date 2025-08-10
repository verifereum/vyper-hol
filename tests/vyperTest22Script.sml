open HolKernel vyperTestRunnerLib vyperTestDefs22Theory;
val () = new_theory "vyperTest22";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs22";
val () = export_theory_no_docs();
