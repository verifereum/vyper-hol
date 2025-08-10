open HolKernel vyperTestRunnerLib vyperTestDefs43Theory;
val () = new_theory "vyperTest43";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs43";
val () = export_theory_no_docs();
