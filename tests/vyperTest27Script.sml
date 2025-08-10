open HolKernel vyperTestRunnerLib vyperTestDefs27Theory;
val () = new_theory "vyperTest27";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs27";
val () = export_theory_no_docs();
