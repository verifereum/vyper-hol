open HolKernel vyperTestRunnerLib vyperTestDefs73Theory;
val () = new_theory "vyperTest73";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs73";
val () = export_theory_no_docs();
