open HolKernel vyperTestLib

val () = new_theory "vyperTestDefs";

val () = make_definitions_for_file 1;
(* TODO: slow val () = make_definitions_for_file 2; *)
val () = List.app make_definitions_for_file $
         List.tabulate (num_test_files - 2, fn i => i + 3);

val () = export_theory_no_docs();
