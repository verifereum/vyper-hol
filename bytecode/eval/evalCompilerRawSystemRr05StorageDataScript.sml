(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemRr05StorageData
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

val rr05_storage_data = memoryStoreWitnessLib.evaluate fixture_root "rr05_storage_data"
Theorem rr05_storage_data_matches_python_oracle:
  ^(#term rr05_storage_data) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rr05_storage_data")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rr05_storage_data))) >> EVAL_TAC
QED
