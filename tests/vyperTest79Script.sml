open HolKernel vyperTestRunnerLib vyperTestDefs79Theory;
val () = new_theory "vyperTest79";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs79";
val () = export_theory_no_docs();
