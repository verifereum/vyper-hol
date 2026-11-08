(* Checked compilation of the p74 internal/external-call fixture. Bounded
   return decoding deliberately differs from the independent VYPER_PIN oracle. *)
Theory evalCompilerInternalFramesExtCall
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../internal-frames"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])

val fixture_root = "../internal-frames/oracle"
val p74_int_ext_call = memoryStoreWitnessLib.evaluate fixture_root "p74_int_ext_call"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "p74_int_ext_call" p74_int_ext_call
