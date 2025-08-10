open HolKernel vyperTestRunnerLib vyperTestDefs08Theory;
val () = new_theory "vyperTest08";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs08";
val () = export_theory_no_docs();
