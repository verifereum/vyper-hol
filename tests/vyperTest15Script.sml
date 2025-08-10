open HolKernel vyperTestRunnerLib vyperTestDefs15Theory;
val () = new_theory "vyperTest15";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs15";
val () = export_theory_no_docs();
