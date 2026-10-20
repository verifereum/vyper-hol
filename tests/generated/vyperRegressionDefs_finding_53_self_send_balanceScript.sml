Theory vyperRegressionDefs_finding_53_self_send_balance[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../fixtures/regression/finding_53_self_send_balance/traces.json"];
val () = make_definitions_for_file ("regression_finding_53_self_send_balance", "../fixtures/regression/finding_53_self_send_balance/traces.json");
