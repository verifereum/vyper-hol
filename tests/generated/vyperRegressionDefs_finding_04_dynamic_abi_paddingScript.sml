Theory vyperRegressionDefs_finding_04_dynamic_abi_padding[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../fixtures/regression/finding_04_dynamic_abi_padding/traces.json"];
val () = make_definitions_for_file ("regression_finding_04_dynamic_abi_padding", "../fixtures/regression/finding_04_dynamic_abi_padding/traces.json");
