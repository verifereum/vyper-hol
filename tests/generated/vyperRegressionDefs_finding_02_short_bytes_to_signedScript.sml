Theory vyperRegressionDefs_finding_02_short_bytes_to_signed[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../fixtures/regression/finding_02_short_bytes_to_signed/traces.json"];
val () = make_definitions_for_file ("regression_finding_02_short_bytes_to_signed", "../fixtures/regression/finding_02_short_bytes_to_signed/traces.json");
