(* Bytecode parity of internal calls that omit default arguments: the call
   appends the callee's omitted defaults, as pinned Python's
   _lower_internal_call does. *)
Theory evalCompilerInternalDefaults
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../internal-defaults"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../internal-defaults/oracle"

val d01_int_default_word = memoryStoreWitnessLib.evaluate fixture_root "d01_int_default_word"
Theorem d01_int_default_word_matches_python_oracle:
  ^(#term d01_int_default_word) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "d01_int_default_word")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation d01_int_default_word))) >> EVAL_TAC
QED

val d02_int_default_partial = memoryStoreWitnessLib.evaluate fixture_root "d02_int_default_partial"
Theorem d02_int_default_partial_matches_python_oracle:
  ^(#term d02_int_default_partial) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "d02_int_default_partial")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation d02_int_default_partial))) >> EVAL_TAC
QED

val d03_int_default_env = memoryStoreWitnessLib.evaluate fixture_root "d03_int_default_env"
Theorem d03_int_default_env_matches_python_oracle:
  ^(#term d03_int_default_env) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "d03_int_default_env")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation d03_int_default_env))) >> EVAL_TAC
QED

val d04_int_default_string = memoryStoreWitnessLib.evaluate fixture_root "d04_int_default_string"
Theorem d04_int_default_string_matches_python_oracle:
  ^(#term d04_int_default_string) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "d04_int_default_string")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation d04_int_default_string))) >> EVAL_TAC
QED


val d05_int_default_nested = memoryStoreWitnessLib.evaluate fixture_root "d05_int_default_nested"
Theorem d05_int_default_nested_matches_python_oracle:
  ^(#term d05_int_default_nested) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "d05_int_default_nested")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation d05_int_default_nested))) >> EVAL_TAC
QED
