(* First-occurrence DFT effect dependencies: interface storage before a staticcall. *)
Theory evalCompilerDftStorageOrder
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../external-calls"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../external-calls/oracle"

(* evaluate checks the exported contract in runtime and deployment modes.
   Only the final equality uses the independently generated Python bytes. *)
val m10c_iface_storage_main =
  memoryStoreWitnessLib.evaluate fixture_root "m10c_iface_storage_main"

Theorem m10c_iface_storage_main_matches_python_oracle:
  ^(#term m10c_iface_storage_main) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "m10c_iface_storage_main")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation m10c_iface_storage_main))) >> EVAL_TAC
QED
