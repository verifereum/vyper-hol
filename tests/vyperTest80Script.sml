open HolKernel vyperTestRunnerLib vyperTestDefs80Theory;
val () = new_theory "vyperTest80";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs80";
val () = export_theory_no_docs();
