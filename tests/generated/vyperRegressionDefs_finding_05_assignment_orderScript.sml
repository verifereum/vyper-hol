Theory vyperRegressionDefs_finding_05_assignment_order[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../fixtures/regression/finding_05_assignment_order/traces.json"];
val () = make_definitions_for_file ("regression_finding_05_assignment_order", "../fixtures/regression/finding_05_assignment_order/traces.json");
