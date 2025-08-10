open HolKernel vyperTestRunnerLib vyperTestDefs78Theory;
val () = new_theory "vyperTest78";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs78";
val () = export_theory_no_docs();
