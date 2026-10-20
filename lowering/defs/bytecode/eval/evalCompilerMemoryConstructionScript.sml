(* Independent pinned-Vyper construction fixtures, checked by the stock frontend. *)
Theory evalCompilerMemoryConstruction
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
fun repository_root dir =
  if OS.FileSys.access (OS.Path.concat (dir, "VYPER_PIN"), []) then dir
  else let val parent = OS.Path.getParent dir in
    if parent = dir then raise Fail "cannot locate repository VYPER_PIN"
    else repository_root parent
  end
val repo_root = repository_root (OS.FileSys.getDir ())
val fixture_root = OS.Path.concat (repo_root, "lowering/defs/bytecode/memory-stores/oracle")
val output_root = OS.Path.concat (repo_root, "lowering/defs/bytecode/memory-construction-results")
val () = (OS.FileSys.mkDir output_root handle OS.SysErr _ => ())
val names = ["tup_nested_ret", "st_nested_lit", "arr_dyn_lit_word", "b20_dynarr_lit", "empty_string_ret", "empty_dynarr_local", "arr_local_elem_assign", "st_empty_ret", "c10_assign_empty_struct", "c11_annassign_empty_fixed_array", "c05_assign_empty_builtin_string"]
val () = List.app (memoryStoreWitnessLib.probe fixture_root output_root) names

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
