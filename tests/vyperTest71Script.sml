open HolKernel vyperTestRunnerLib vyperTestDefs71Theory;
val () = new_theory "vyperTest71";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs71";
val () = export_theory_no_docs();
