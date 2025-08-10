open HolKernel vyperTestRunnerLib vyperTestDefs69Theory;
val () = new_theory "vyperTest69";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs69";
val () = export_theory_no_docs();
