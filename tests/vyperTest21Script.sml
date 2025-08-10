open HolKernel vyperTestRunnerLib vyperTestDefs21Theory;
val () = new_theory "vyperTest21";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs21";
val () = export_theory_no_docs();
