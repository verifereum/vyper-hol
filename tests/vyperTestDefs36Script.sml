open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs36";
val () = make_definitions_for_file (36, "../../vyper/tests/export/functional/codegen/types/numbers/test_unsigned_ints.json");
val () = export_theory_no_docs();
