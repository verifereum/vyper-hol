open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs76";
val () = make_definitions_for_file (76, "../../vyper/tests/export/functional/codegen/features/decorators/test_public.json");
val () = export_theory_no_docs();
