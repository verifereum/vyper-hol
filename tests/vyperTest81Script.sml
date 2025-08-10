open HolKernel vyperTestRunnerLib vyperTestDefs81Theory;
val () = new_theory "vyperTest81";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs81";
val () = export_theory_no_docs();
