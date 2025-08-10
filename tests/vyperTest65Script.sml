open HolKernel vyperTestRunnerLib vyperTestDefs65Theory;
val () = new_theory "vyperTest65";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs65";
val () = export_theory_no_docs();
