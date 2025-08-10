open HolKernel vyperTestRunnerLib vyperTestDefs04Theory;
val () = new_theory "vyperTest04";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs04";
val () = export_theory_no_docs();
