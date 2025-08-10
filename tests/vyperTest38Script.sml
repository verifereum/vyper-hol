open HolKernel vyperTestRunnerLib vyperTestDefs38Theory;
val () = new_theory "vyperTest38";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs38";
val () = export_theory_no_docs();
