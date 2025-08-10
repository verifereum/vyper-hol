open HolKernel vyperTestRunnerLib vyperTestDefs72Theory;
val () = new_theory "vyperTest72";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs72";
val () = export_theory_no_docs();
