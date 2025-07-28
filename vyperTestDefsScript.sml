open HolKernel vyperTestLib

val () = new_theory "vyperTestDefs";

val () = make_definitions_for_file 1;
(* TODO: slow val () = make_definitions_for_file 2; *)
val () = make_definitions_for_file 3;
val () = make_definitions_for_file 4;

val () = export_theory_no_docs();
