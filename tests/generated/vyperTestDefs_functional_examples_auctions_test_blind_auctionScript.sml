Theory vyperTestDefs_functional_examples_auctions_test_blind_auction[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/examples/auctions/test_blind_auction.json", "../vyper-test-exports/functional/examples/auctions/test_blind_auction.json.provenance", "../../VYPER_PIN", "../semantics-profile.json", "../semantics-test-constraints.txt", "../semantics-build-constraints.txt", "../../tools/vyper_test_exports.py", "../../tools/vyper_test_export_plugin.py", "../../.github/actions/setup-vyper-test-exports/action.yml", "../vyper-regression"];
val () = make_definitions_for_file_range ("functional_examples_auctions_test_blind_auction", "../vyper-test-exports/functional/examples/auctions/test_blind_auction.json", 0, 4);
