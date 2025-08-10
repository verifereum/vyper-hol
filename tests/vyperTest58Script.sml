open HolKernel vyperTestRunnerLib vyperTestDefs58Theory;
val () = new_theory "vyperTest58";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs58";
val () = export_theory_no_docs();
