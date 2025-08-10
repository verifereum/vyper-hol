open HolKernel vyperTestRunnerLib vyperTestDefs70Theory;
val () = new_theory "vyperTest70";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs70";
val () = export_theory_no_docs();
