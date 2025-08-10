open HolKernel vyperTestRunnerLib vyperTestDefs68Theory;
val () = new_theory "vyperTest68";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs68";
val () = export_theory_no_docs();
