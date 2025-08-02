open HolKernel vyperTestLib

val () = new_theory "vyperTestDefs";

val () = List.app make_definitions_for_file $
         List.tabulate (num_test_files, curry (+) 1);

val () = export_theory_no_docs();
