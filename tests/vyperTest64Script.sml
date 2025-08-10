open HolKernel vyperTestRunnerLib vyperTestDefs64Theory;
val () = new_theory "vyperTest64";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs64";
val () = export_theory_no_docs();
