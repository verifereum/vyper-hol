(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemXaBytesLitReturn
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../raw-system"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../raw-system/oracle"

val xa_bytes_lit_return = memoryStoreWitnessLib.evaluate fixture_root "xa_bytes_lit_return"
Theorem xa_bytes_lit_return_matches_python_oracle:
  ^(#term xa_bytes_lit_return) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "xa_bytes_lit_return")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation xa_bytes_lit_return))) >> EVAL_TAC
QED
