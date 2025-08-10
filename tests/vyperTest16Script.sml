open HolKernel vyperTestRunnerLib vyperTestDefs16Theory;
val () = new_theory "vyperTest16";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs16";
val () = export_theory_no_docs();
