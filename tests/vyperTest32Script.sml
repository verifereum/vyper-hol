open HolKernel vyperTestRunnerLib vyperTestDefs32Theory;
val () = new_theory "vyperTest32";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs32";
val () = export_theory_no_docs();
