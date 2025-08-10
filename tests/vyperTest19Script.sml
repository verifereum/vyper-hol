open HolKernel vyperTestRunnerLib vyperTestDefs19Theory;
val () = new_theory "vyperTest19";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs19";
val () = export_theory_no_docs();
