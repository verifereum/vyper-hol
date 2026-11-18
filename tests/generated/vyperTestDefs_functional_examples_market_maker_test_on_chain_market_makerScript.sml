Theory vyperTestDefs_functional_examples_market_maker_test_on_chain_market_maker[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/examples/market_maker/test_on_chain_market_maker.json", "../vyper-test-exports/functional/examples/market_maker/test_on_chain_market_maker.json.provenance", "../../VYPER_PIN", "../semantics-profile.json", "../semantics-test-constraints.txt", "../semantics-build-constraints.txt", "../../tools/vyper_test_exports.py", "../../tools/vyper_test_export_plugin.py", "../../.github/actions/setup-vyper-test-exports/action.yml", "../vyper-regression"];
val () = make_definitions_for_file ("functional_examples_market_maker_test_on_chain_market_maker", "../vyper-test-exports/functional/examples/market_maker/test_on_chain_market_maker.json");
