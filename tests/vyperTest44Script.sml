open HolKernel vyperTestRunnerLib vyperTestDefs44Theory;
val () = new_theory "vyperTest44";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs44";
val () = export_theory_no_docs();
