(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityI13PublicImmutAddress
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib compilerParityCompsetLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = compilerParityCompsetLib.prepare {byte_updates = false}
val fixture_root = "../getters-constants/oracle"

val i13_public_immut_address = memoryStoreWitnessLib.evaluate fixture_root "i13_public_immut_address"
Theorem i13_public_immut_address_matches_python_oracle:
  ^(#term i13_public_immut_address) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "i13_public_immut_address")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation i13_public_immut_address))) >> EVAL_TAC
QED
