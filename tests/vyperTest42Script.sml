open HolKernel vyperTestRunnerLib vyperTestDefs42Theory;
val () = new_theory "vyperTest42";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs42";
val () = export_theory_no_docs();
