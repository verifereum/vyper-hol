open HolKernel vyperTestRunnerLib vyperTestDefs25Theory;
val () = new_theory "vyperTest25";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs25";
val () = export_theory_no_docs();
