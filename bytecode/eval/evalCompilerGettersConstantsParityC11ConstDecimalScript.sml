(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityC11ConstDecimal
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib compilerParityCompsetLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = compilerParityCompsetLib.prepare {byte_updates = false}
val fixture_root = "../getters-constants/oracle"

val c11_const_decimal = memoryStoreWitnessLib.evaluate fixture_root "c11_const_decimal"
Theorem c11_const_decimal_matches_python_oracle:
  ^(#term c11_const_decimal) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c11_const_decimal")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c11_const_decimal))) >> EVAL_TAC
QED
