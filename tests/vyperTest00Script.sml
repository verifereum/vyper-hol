open HolKernel vyperTestRunnerLib vyperTestDefs00Theory;
val () = new_theory "vyperTest00";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs00";
val () = export_theory_no_docs();
