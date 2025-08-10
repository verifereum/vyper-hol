open HolKernel vyperTestRunnerLib vyperTestDefs56Theory;
val () = new_theory "vyperTest56";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs56";
val () = export_theory_no_docs();
