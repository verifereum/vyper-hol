open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs77";
val () = make_definitions_for_file (77, "../../vyper/tests/export/functional/codegen/features/decorators/test_pure.json");
val () = export_theory_no_docs();
