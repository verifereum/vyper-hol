open HolKernel vyperTestRunnerLib vyperTestDefs01Theory;
val () = new_theory "vyperTest01";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs01";
val () = export_theory_no_docs();
