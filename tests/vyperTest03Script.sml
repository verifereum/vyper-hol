open HolKernel vyperTestRunnerLib vyperTestDefs03Theory;
val () = new_theory "vyperTest03";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs03";
val () = export_theory_no_docs();
