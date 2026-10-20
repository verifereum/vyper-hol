Theory vyperRegressionDefs_finding_14_send_revert[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../fixtures/regression/finding_14_send_revert/traces.json"];
val () = make_definitions_for_file ("regression_finding_14_send_revert", "../fixtures/regression/finding_14_send_revert/traces.json");
