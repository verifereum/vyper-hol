open HolKernel vyperTestRunnerLib vyperTestDefs51Theory;
val () = new_theory "vyperTest51";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs51";
val () = export_theory_no_docs();
