Theory vyperRegressionDefs_finding_12_address_widening[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../fixtures/regression/finding_12_address_widening/traces.json"];
val () = make_definitions_for_file ("regression_finding_12_address_widening", "../fixtures/regression/finding_12_address_widening/traces.json");
