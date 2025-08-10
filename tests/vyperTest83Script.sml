open HolKernel vyperTestRunnerLib vyperTestDefs83Theory;
val () = new_theory "vyperTest83";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs83";
val () = export_theory_no_docs();
