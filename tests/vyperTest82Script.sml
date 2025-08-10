open HolKernel vyperTestRunnerLib vyperTestDefs82Theory;
val () = new_theory "vyperTest82";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs82";
val () = export_theory_no_docs();
