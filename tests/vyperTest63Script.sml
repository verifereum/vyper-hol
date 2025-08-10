open HolKernel vyperTestRunnerLib vyperTestDefs63Theory;
val () = new_theory "vyperTest63";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs63";
val () = export_theory_no_docs();
