open HolKernel vyperTestRunnerLib vyperTestDefs09Theory;
val () = new_theory "vyperTest09";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs09";
val () = export_theory_no_docs();
