open HolKernel vyperTestRunnerLib vyperTestDefs50Theory;
val () = new_theory "vyperTest50";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs50";
val () = export_theory_no_docs();
