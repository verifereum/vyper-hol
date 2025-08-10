open HolKernel vyperTestRunnerLib vyperTestDefs49Theory;
val () = new_theory "vyperTest49";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs49";
val () = export_theory_no_docs();
