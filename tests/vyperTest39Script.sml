open HolKernel vyperTestRunnerLib vyperTestDefs39Theory;
val () = new_theory "vyperTest39";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs39";
val () = export_theory_no_docs();
