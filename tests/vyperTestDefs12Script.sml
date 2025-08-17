open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs12";
val () = make_definitions_for_file (12, "../../vyper/tests/export/functional/codegen/environment_variables/test_block_number.json");
val () = export_theory_no_docs();
