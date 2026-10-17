Theory vyperTestDefs_functional_codegen_abstract_test_events[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/abstract/test_events.json"];
val () = make_definitions_for_file ("functional_codegen_abstract_test_events", "../vyper-test-exports/functional/codegen/abstract/test_events.json");
