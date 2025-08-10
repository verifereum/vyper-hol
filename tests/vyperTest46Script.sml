open HolKernel vyperTestRunnerLib vyperTestDefs46Theory;
val () = new_theory "vyperTest46";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs46";
val () = export_theory_no_docs();
