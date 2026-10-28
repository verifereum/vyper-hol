(* Independent pinned-Vyper construction fixtures, checked by the stock frontend. *)
Theory evalCompilerMemoryConstruction
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../memory-stores"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../memory-stores/oracle"

val tup_nested_ret = memoryStoreWitnessLib.evaluate fixture_root "tup_nested_ret"
Theorem tup_nested_ret_matches_python_oracle:
  ^(#term tup_nested_ret) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "tup_nested_ret")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation tup_nested_ret))) >> EVAL_TAC
QED
val st_nested_lit = memoryStoreWitnessLib.evaluate fixture_root "st_nested_lit"
Theorem st_nested_lit_matches_python_oracle:
  ^(#term st_nested_lit) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "st_nested_lit")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation st_nested_lit))) >> EVAL_TAC
QED
(* S names T before T's declaration: T must still be laid out as two words. *)
val st_forward_ref_lit = memoryStoreWitnessLib.evaluate fixture_root "st_forward_ref_lit"
Theorem st_forward_ref_lit_matches_python_oracle:
  ^(#term st_forward_ref_lit) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "st_forward_ref_lit")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation st_forward_ref_lit))) >> EVAL_TAC
QED
val arr_dyn_lit_word = memoryStoreWitnessLib.evaluate fixture_root "arr_dyn_lit_word"
Theorem arr_dyn_lit_word_matches_python_oracle:
  ^(#term arr_dyn_lit_word) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "arr_dyn_lit_word")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation arr_dyn_lit_word))) >> EVAL_TAC
QED
val b20_dynarr_lit = memoryStoreWitnessLib.evaluate fixture_root "b20_dynarr_lit"
Theorem b20_dynarr_lit_matches_python_oracle:
  ^(#term b20_dynarr_lit) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "b20_dynarr_lit")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation b20_dynarr_lit))) >> EVAL_TAC
QED
val empty_string_ret = memoryStoreWitnessLib.evaluate fixture_root "empty_string_ret"
Theorem empty_string_ret_matches_python_oracle:
  ^(#term empty_string_ret) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "empty_string_ret")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation empty_string_ret))) >> EVAL_TAC
QED
val empty_dynarr_local = memoryStoreWitnessLib.evaluate fixture_root "empty_dynarr_local"
Theorem empty_dynarr_local_matches_python_oracle:
  ^(#term empty_dynarr_local) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "empty_dynarr_local")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation empty_dynarr_local))) >> EVAL_TAC
QED
val arr_local_elem_assign = memoryStoreWitnessLib.evaluate fixture_root "arr_local_elem_assign"
Theorem arr_local_elem_assign_matches_python_oracle:
  ^(#term arr_local_elem_assign) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "arr_local_elem_assign")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation arr_local_elem_assign))) >> EVAL_TAC
QED
val st_empty_ret = memoryStoreWitnessLib.evaluate fixture_root "st_empty_ret"
Theorem st_empty_ret_matches_python_oracle:
  ^(#term st_empty_ret) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "st_empty_ret")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation st_empty_ret))) >> EVAL_TAC
QED
val c10 = memoryStoreWitnessLib.evaluate fixture_root "c10_assign_empty_struct"
Theorem c10_assign_empty_struct_matches_python_oracle:
  ^(#term c10) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c10_assign_empty_struct")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c10))) >> EVAL_TAC
QED
val c11 = memoryStoreWitnessLib.evaluate fixture_root "c11_annassign_empty_fixed_array"
Theorem c11_annassign_empty_fixed_array_matches_python_oracle:
  ^(#term c11) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c11_annassign_empty_fixed_array")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c11))) >> EVAL_TAC
QED
val c05 = memoryStoreWitnessLib.evaluate fixture_root "c05_assign_empty_builtin_string"
Theorem c05_assign_empty_builtin_string_matches_python_oracle:
  ^(#term c05) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c05_assign_empty_builtin_string")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c05))) >> EVAL_TAC
QED
