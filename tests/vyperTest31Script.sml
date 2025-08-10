open HolKernel vyperTestRunnerLib vyperTestDefs31Theory;
val () = new_theory "vyperTest31";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs31";
val () = export_theory_no_docs();
