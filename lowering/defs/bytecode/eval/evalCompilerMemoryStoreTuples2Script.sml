(* Independent checked-frontend bytecode witnesses for memory stores.
   Half 2 of evalCompilerMemoryStoreTuples: t03_tuple_assign_abi_decode,
   t06_tuple_assign_mixed_targets, t07_tuple_assign_string_elems,
   t11_tuple_onew_decode_mem. *)
Theory evalCompilerMemoryStoreTuples2
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../memory-stores/oracle/t03_tuple_assign_abi_decode.json",
   "../memory-stores/oracle/t03_tuple_assign_abi_decode.hex",
   "../memory-stores/oracle/t06_tuple_assign_mixed_targets.json",
   "../memory-stores/oracle/t06_tuple_assign_mixed_targets.hex",
   "../memory-stores/oracle/t07_tuple_assign_string_elems.json",
   "../memory-stores/oracle/t07_tuple_assign_string_elems.hex",
   "../memory-stores/oracle/t11_tuple_onew_decode_mem.json",
   "../memory-stores/oracle/t11_tuple_onew_decode_mem.hex"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../memory-stores/oracle"

val t03_tuple_assign_abi_decode = memoryStoreWitnessLib.evaluate fixture_root "t03_tuple_assign_abi_decode"
Theorem t03_tuple_assign_abi_decode_matches_python_oracle:
  ^(#term t03_tuple_assign_abi_decode) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "t03_tuple_assign_abi_decode")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation t03_tuple_assign_abi_decode))) >> EVAL_TAC
QED

val t06_tuple_assign_mixed_targets = memoryStoreWitnessLib.evaluate fixture_root "t06_tuple_assign_mixed_targets"
Theorem t06_tuple_assign_mixed_targets_matches_python_oracle:
  ^(#term t06_tuple_assign_mixed_targets) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "t06_tuple_assign_mixed_targets")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation t06_tuple_assign_mixed_targets))) >> EVAL_TAC
QED

val t07_tuple_assign_string_elems = memoryStoreWitnessLib.evaluate fixture_root "t07_tuple_assign_string_elems"
Theorem t07_tuple_assign_string_elems_matches_python_oracle:
  ^(#term t07_tuple_assign_string_elems) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "t07_tuple_assign_string_elems")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation t07_tuple_assign_string_elems))) >> EVAL_TAC
QED

val t11_tuple_onew_decode_mem = memoryStoreWitnessLib.evaluate fixture_root "t11_tuple_onew_decode_mem"
Theorem t11_tuple_onew_decode_mem_matches_python_oracle:
  ^(#term t11_tuple_onew_decode_mem) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "t11_tuple_onew_decode_mem")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation t11_tuple_onew_decode_mem))) >> EVAL_TAC
QED
