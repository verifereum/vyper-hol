open HolKernel vyperTestRunnerLib vyperTestDefs11Theory;
val () = new_theory "vyperTest11";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs11";
val () = export_theory_no_docs();
