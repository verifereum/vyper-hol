open HolKernel vyperTestRunnerLib vyperTestDefs07Theory;
val () = new_theory "vyperTest07";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs07";
val () = export_theory_no_docs();
