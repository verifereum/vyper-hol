open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs73";
val () = make_definitions_for_file (73, "../../vyper/tests/export/functional/codegen/features/decorators/test_nonreentrant.json");
val () = export_theory_no_docs();
