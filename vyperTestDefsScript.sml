open HolKernel vyperTestLib

val () = new_theory "vyperTestDefs";

val () = make_definitions_for_file 1;
val () = make_definitions_for_file 2;

val () = export_theory_no_docs();
