open HolKernel vyperTestRunnerLib vyperTestDefs74Theory;
val () = new_theory "vyperTest74";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs74";
val () = export_theory_no_docs();
