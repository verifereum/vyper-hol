Theory vyperTestDefs_functional_syntax_test_address_code[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/syntax/test_address_code.json", "../vyper-test-exports/functional/syntax/test_address_code.json.provenance", "../../VYPER_PIN", "../semantics-profile.json", "../semantics-test-constraints.txt", "../semantics-build-constraints.txt", "../../tools/vyper_test_exports.py", "../../tools/vyper_test_export_plugin.py", "../../.github/actions/setup-vyper-test-exports/action.yml", "../vyper-regression"];
val () = make_definitions_for_file ("functional_syntax_test_address_code", "../vyper-test-exports/functional/syntax/test_address_code.json");
