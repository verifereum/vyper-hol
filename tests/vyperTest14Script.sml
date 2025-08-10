open HolKernel vyperTestRunnerLib vyperTestDefs14Theory;
val () = new_theory "vyperTest14";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs14";
val () = export_theory_no_docs();
