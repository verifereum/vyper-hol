(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltins1
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../create-builtins"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../create-builtins/oracle"

val nest01_create_in_call = memoryStoreWitnessLib.evaluate fixture_root "nest01_create_in_call"
Theorem nest01_create_in_call_matches_python_oracle:
  ^(#term nest01_create_in_call) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nest01_create_in_call")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nest01_create_in_call))) >> EVAL_TAC
QED

val cc02_copy_salt_value = memoryStoreWitnessLib.evaluate fixture_root "cc02_copy_salt_value"
Theorem cc02_copy_salt_value_matches_python_oracle:
  ^(#term cc02_copy_salt_value) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cc02_copy_salt_value")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cc02_copy_salt_value))) >> EVAL_TAC
QED

val cc03_copy_rof = memoryStoreWitnessLib.evaluate fixture_root "cc03_copy_rof"
Theorem cc03_copy_rof_matches_python_oracle:
  ^(#term cc03_copy_rof) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cc03_copy_rof")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cc03_copy_rof))) >> EVAL_TAC
QED

val nest02_stmt_create = memoryStoreWitnessLib.evaluate fixture_root "nest02_stmt_create"
Theorem nest02_stmt_create_matches_python_oracle:
  ^(#term nest02_stmt_create) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nest02_stmt_create")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nest02_stmt_create))) >> EVAL_TAC
QED

