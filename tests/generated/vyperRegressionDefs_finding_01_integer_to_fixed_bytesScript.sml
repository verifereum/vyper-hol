Theory vyperRegressionDefs_finding_01_integer_to_fixed_bytes[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../fixtures/regression/finding_01_integer_to_fixed_bytes/traces.json"];
val () = make_definitions_for_file ("regression_finding_01_integer_to_fixed_bytes", "../fixtures/regression/finding_01_integer_to_fixed_bytes/traces.json");
