open HolKernel vyperTestRunnerLib vyperTestDefs67Theory;
val () = new_theory "vyperTest67";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs67";
val () = export_theory_no_docs();
