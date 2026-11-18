Theory evalAssignmentOrderS11StorageMapAssignExtcallRhs
Ancestors
  evalAssignmentOrder compileVyper supportedProgram
  concretizeMemLocDefs codegenReadyCompute
Libs assignmentOrderWitnessLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../assignment-order/oracle"]

val () = assignmentOrderWitnessLib.check_decoder_divergence_fixture "s11_storage_map_assign_extcall_rhs";
