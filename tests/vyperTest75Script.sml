open HolKernel vyperTestRunnerLib vyperTestDefs75Theory;
val () = new_theory "vyperTest75";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs75";
val () = export_theory_no_docs();
