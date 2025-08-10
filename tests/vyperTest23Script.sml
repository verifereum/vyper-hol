open HolKernel vyperTestRunnerLib vyperTestDefs23Theory;
val () = new_theory "vyperTest23";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs23";
val () = export_theory_no_docs();
