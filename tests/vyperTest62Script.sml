open HolKernel vyperTestRunnerLib vyperTestDefs62Theory;
val () = new_theory "vyperTest62";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs62";
val () = export_theory_no_docs();
