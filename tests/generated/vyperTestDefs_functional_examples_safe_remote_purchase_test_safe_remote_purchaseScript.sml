Theory vyperTestDefs_functional_examples_safe_remote_purchase_test_safe_remote_purchase[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/examples/safe_remote_purchase/test_safe_remote_purchase.json", "../vyper-test-exports/functional/examples/safe_remote_purchase/test_safe_remote_purchase.json.provenance", "../../VYPER_PIN", "../semantics-profile.json", "../semantics-test-constraints.txt", "../semantics-build-constraints.txt", "../../tools/vyper_test_exports.py", "../../tools/vyper_test_export_plugin.py", "../../.github/actions/setup-vyper-test-exports/action.yml", "../vyper-regression"];
val () = make_definitions_for_file ("functional_examples_safe_remote_purchase_test_safe_remote_purchase", "../vyper-test-exports/functional/examples/safe_remote_purchase/test_safe_remote_purchase.json");
