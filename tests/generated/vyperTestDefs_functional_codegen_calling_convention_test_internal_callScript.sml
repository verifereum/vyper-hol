Theory vyperTestDefs_functional_codegen_calling_convention_test_internal_call[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/calling_convention/test_internal_call.json", "../vyper-test-exports/functional/codegen/calling_convention/test_internal_call.json.provenance", "../../VYPER_PIN", "../semantics-profile.json", "../semantics-test-constraints.txt", "../semantics-build-constraints.txt", "../../tools/vyper_test_exports.py", "../../tools/vyper_test_export_plugin.py", "../../.github/actions/setup-vyper-test-exports/action.yml", "../vyper-regression"];
val () = make_definitions_for_file_range ("functional_codegen_calling_convention_test_internal_call", "../vyper-test-exports/functional/codegen/calling_convention/test_internal_call.json", 0, 27);
