Theory evalAssignmentOrderX04AssignSideeffectOrder
Ancestors
  evalAssignmentOrder compileVyper supportedProgram
  concretizeMemLocDefs codegenReadyCompute
Libs assignmentOrderWitnessLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../assignment-order/oracle"]

val () = assignmentOrderWitnessLib.check_compiler_fixture "x04_assign_sideeffect_order";
