open HolKernel vyperTestRunnerLib vyperTestDefs37Theory;
val () = new_theory "vyperTest37";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs37";
val () = export_theory_no_docs();
