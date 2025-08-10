open HolKernel vyperTestRunnerLib vyperTestDefs59Theory;
val () = new_theory "vyperTest59";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs59";
val () = export_theory_no_docs();
