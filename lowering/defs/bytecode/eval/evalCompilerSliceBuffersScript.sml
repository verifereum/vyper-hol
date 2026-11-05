(* Independent checked-frontend bytecode witnesses for slice output buffers
   (#561, a07-06).
   TOP-LEVEL: slice_storage_bytes_matches_python_oracle. *)
Theory evalCompilerSliceBuffers
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../slice-buffers"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../slice-buffers/oracle"

(* control: storage Bytes source. *)
val slice_storage_bytes = memoryStoreWitnessLib.evaluate fixture_root "slice_storage_bytes"
Theorem slice_storage_bytes_matches_python_oracle:
  ^(#term slice_storage_bytes) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "slice_storage_bytes")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation slice_storage_bytes))) >> EVAL_TAC
QED
