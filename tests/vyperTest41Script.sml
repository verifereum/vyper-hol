open HolKernel vyperTestRunnerLib vyperTestDefs41Theory;
val () = new_theory "vyperTest41";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs41";
val () = export_theory_no_docs();
