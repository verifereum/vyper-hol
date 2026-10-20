Theory vyperRegressionDefs_finding_40_block_gaslimit[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../fixtures/regression/finding_40_block_gaslimit/traces.json"];
val () = make_definitions_for_file ("regression_finding_40_block_gaslimit", "../fixtures/regression/finding_40_block_gaslimit/traces.json");
