open HolKernel vyperTestRunnerLib vyperTestDefs17Theory;
val () = new_theory "vyperTest17";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs17";
val () = export_theory_no_docs();
