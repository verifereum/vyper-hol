open HolKernel vyperTestRunnerLib vyperTestDefs34Theory;
val () = new_theory "vyperTest34";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs34";
val () = export_theory_no_docs();
