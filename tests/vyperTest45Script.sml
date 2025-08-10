open HolKernel vyperTestRunnerLib vyperTestDefs45Theory;
val () = new_theory "vyperTest45";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs45";
val () = export_theory_no_docs();
