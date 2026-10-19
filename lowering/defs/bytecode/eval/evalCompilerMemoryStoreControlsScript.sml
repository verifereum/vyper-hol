(* Independent checked-frontend bytecode witnesses for memory stores. *)
Theory evalCompilerMemoryStoreControls
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../memory-stores"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../memory-stores/oracle"

val c01_ctrl_str_local_decl = memoryStoreWitnessLib.evaluate fixture_root "c01_ctrl_str_local_decl"
Theorem c01_ctrl_str_local_decl_matches_python_oracle:
  ^(#term c01_ctrl_str_local_decl) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "c01_ctrl_str_local_decl")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c01_ctrl_str_local_decl))) >> EVAL_TAC
QED

val c07_annassign_str_same_len = memoryStoreWitnessLib.evaluate fixture_root "c07_annassign_str_same_len"
Theorem c07_annassign_str_same_len_matches_python_oracle:
  ^(#term c07_annassign_str_same_len) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "c07_annassign_str_same_len")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c07_annassign_str_same_len))) >> EVAL_TAC
QED

val c12_annassign_empty_bytes_ret = memoryStoreWitnessLib.evaluate fixture_root "c12_annassign_empty_bytes_ret"
Theorem c12_annassign_empty_bytes_ret_matches_python_oracle:
  ^(#term c12_annassign_empty_bytes_ret) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "c12_annassign_empty_bytes_ret")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c12_annassign_empty_bytes_ret))) >> EVAL_TAC
QED
