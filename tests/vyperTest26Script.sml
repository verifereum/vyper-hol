open HolKernel vyperTestRunnerLib vyperTestDefs26Theory;
val () = new_theory "vyperTest26";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs26";
val () = export_theory_no_docs();
