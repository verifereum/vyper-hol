(* Independent checked-frontend bytecode witnesses for external-call
   arguments whose type is narrower than the declared parameter type: the
   argument buffer is laid out with the call-site types. *)
Theory evalCompilerExternalCallArgTypes
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../external-calls"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../external-calls/oracle"

val e25_arg_strlit_short = memoryStoreWitnessLib.evaluate fixture_root "e25_arg_strlit_short"
Theorem e25_arg_strlit_short_matches_python_oracle:
  ^(#term e25_arg_strlit_short) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e25_arg_strlit_short")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e25_arg_strlit_short))) >> EVAL_TAC
QED

val e36_arg_bytes_literal = memoryStoreWitnessLib.evaluate fixture_root "e36_arg_bytes_literal"
Theorem e36_arg_bytes_literal_matches_python_oracle:
  ^(#term e36_arg_bytes_literal) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e36_arg_bytes_literal")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e36_arg_bytes_literal))) >> EVAL_TAC
QED
