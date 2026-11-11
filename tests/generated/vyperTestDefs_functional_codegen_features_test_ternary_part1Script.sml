Theory vyperTestDefs_functional_codegen_features_test_ternary_part1[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/features/test_ternary.json", "../vyper-test-exports/functional/codegen/features/test_ternary.json.provenance", "../../VYPER_PIN", "../semantics-profile.json", "../semantics-test-constraints.txt", "../semantics-build-constraints.txt", "../../tools/vyper_test_exports.py", "../../tools/vyper_test_export_plugin.py", "../../.github/actions/setup-vyper-test-exports/action.yml", "../vyper-regression"];
val () = make_definitions_for_file_range ("functional_codegen_features_test_ternary", "../vyper-test-exports/functional/codegen/features/test_ternary.json", 100, 100);
