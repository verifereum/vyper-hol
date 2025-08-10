open HolKernel vyperTestRunnerLib vyperTestDefs52Theory;
val () = new_theory "vyperTest52";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs52";
val () = export_theory_no_docs();
