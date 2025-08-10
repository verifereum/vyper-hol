open HolKernel vyperTestRunnerLib vyperTestDefs18Theory;
val () = new_theory "vyperTest18";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs18";
val () = export_theory_no_docs();
