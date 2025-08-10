open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs79";
val () = make_definitions_for_file (79, "../../vyper/tests/export/functional/codegen/features/decorators/test_raw_return.json");
val () = export_theory_no_docs();
