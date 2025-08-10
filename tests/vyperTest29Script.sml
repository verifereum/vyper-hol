open HolKernel vyperTestRunnerLib vyperTestDefs29Theory;
val () = new_theory "vyperTest29";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs29";
val () = export_theory_no_docs();
