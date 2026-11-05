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

(* evaluate checks runtime and deployment modes. Bounded return decoding
   intentionally differs from the pinned Python compiler. *)
val m10c_iface_storage_main =
  memoryStoreWitnessLib.evaluate fixture_root "m10c_iface_storage_main"

val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "m10c_iface_storage_main" m10c_iface_storage_main
