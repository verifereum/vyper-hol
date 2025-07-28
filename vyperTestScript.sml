open HolKernel vyperTestDefsTheory vyperTestLib

val () = new_theory "vyperTest";

val all_constants = constants "vyperTestDefs";
val traces = List.filter (equal traces_ty o #2 o dest_const) all_constants;
val () = List.app run_test_on_traces traces;

val () = export_theory_no_docs();
