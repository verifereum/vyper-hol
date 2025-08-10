open HolKernel vyperTestRunnerLib vyperTestDefs77Theory;
val () = new_theory "vyperTest77";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs77";
val () = export_theory_no_docs();
