(* Independent checked-frontend bytecode witnesses for For over an array
   (#559): the iterable's shape, length and element type come from its type
   and its location from its compiled value, the DynArray bound check sits
   in the entry block, and slot-addressed elements are copied by the
   word-copy loop, all as Python's _lower_iter_loop.
   TOP-LEVEL: f05_for_literal_list_matches_python_oracle,
              f20_for_list_of_vars_matches_python_oracle,
              f03_for_storage_dynarray_matches_python_oracle,
              f04_for_storage_fixed_matches_python_oracle,
              g8_a_iter_transient_matches_python_oracle,
              g8_a_iter_struct_elem_matches_python_oracle,
              f23_for_local_fixed_matches_python_oracle,
              f24_for_local_dynarray_matches_python_oracle,
              f01_for_calldata_dynarray_matches_python_oracle,
              f06_for_calldata_fixed_matches_python_oracle,
              f50_for_subscript_row_matches_python_oracle,
              f38_for_storage_struct_field_arr_set_matches_python_oracle. *)
Theory evalCompilerForIterables
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../for-iterables"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../for-iterables/oracle"

(* a uint256[3] list literal: iterated as a fixed array (was read as a DynArray, element 0 taken as the length). *)
val f05_for_literal_list = memoryStoreWitnessLib.evaluate fixture_root "f05_for_literal_list"
Theorem f05_for_literal_list_matches_python_oracle:
  ^(#term f05_for_literal_list) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "f05_for_literal_list")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation f05_for_literal_list))) >> EVAL_TAC
QED

(* a list literal of variables: the same (was a reverting length check). *)
val f20_for_list_of_vars = memoryStoreWitnessLib.evaluate fixture_root "f20_for_list_of_vars"
Theorem f20_for_list_of_vars_matches_python_oracle:
  ^(#term f20_for_list_of_vars) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "f20_for_list_of_vars")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation f20_for_list_of_vars))) >> EVAL_TAC
QED

(* a storage DynArray: the bound check is in the entry block and each element is copied by the slot word-copy loop. *)
val f03_for_storage_dynarray = memoryStoreWitnessLib.evaluate fixture_root "f03_for_storage_dynarray"
Theorem f03_for_storage_dynarray_matches_python_oracle:
  ^(#term f03_for_storage_dynarray) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "f03_for_storage_dynarray")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation f03_for_storage_dynarray))) >> EVAL_TAC
QED

(* a storage fixed array of one-slot elements: the slot word-copy loop (was SLOAD + MSTORE). *)
val f04_for_storage_fixed = memoryStoreWitnessLib.evaluate fixture_root "f04_for_storage_fixed"
Theorem f04_for_storage_fixed_matches_python_oracle:
  ^(#term f04_for_storage_fixed) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "f04_for_storage_fixed")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation f04_for_storage_fixed))) >> EVAL_TAC
QED

(* a transient fixed array: the same with TLOAD. *)
val g8_a_iter_transient = memoryStoreWitnessLib.evaluate fixture_root "g8_a_iter_transient"
Theorem g8_a_iter_transient_matches_python_oracle:
  ^(#term g8_a_iter_transient) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "g8_a_iter_transient")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g8_a_iter_transient))) >> EVAL_TAC
QED

(* a storage array of two-slot structs. *)
val g8_a_iter_struct_elem = memoryStoreWitnessLib.evaluate fixture_root "g8_a_iter_struct_elem"
Theorem g8_a_iter_struct_elem_matches_python_oracle:
  ^(#term g8_a_iter_struct_elem) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "g8_a_iter_struct_elem")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g8_a_iter_struct_elem))) >> EVAL_TAC
QED

(* a memory local fixed array (control, supported). *)
val f23_for_local_fixed = memoryStoreWitnessLib.evaluate fixture_root "f23_for_local_fixed"
Theorem f23_for_local_fixed_matches_python_oracle:
  ^(#term f23_for_local_fixed) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "f23_for_local_fixed")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation f23_for_local_fixed))) >> EVAL_TAC
QED

(* a memory local DynArray: the bound check is in the entry block. *)
val f24_for_local_dynarray = memoryStoreWitnessLib.evaluate fixture_root "f24_for_local_dynarray"
Theorem f24_for_local_dynarray_matches_python_oracle:
  ^(#term f24_for_local_dynarray) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "f24_for_local_dynarray")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation f24_for_local_dynarray))) >> EVAL_TAC
QED

(* a DynArray argument: the bound check is in the entry block. *)
val f01_for_calldata_dynarray = memoryStoreWitnessLib.evaluate fixture_root "f01_for_calldata_dynarray"
Theorem f01_for_calldata_dynarray_matches_python_oracle:
  ^(#term f01_for_calldata_dynarray) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "f01_for_calldata_dynarray")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation f01_for_calldata_dynarray))) >> EVAL_TAC
QED

(* a fixed array argument (control, supported). *)
val f06_for_calldata_fixed = memoryStoreWitnessLib.evaluate fixture_root "f06_for_calldata_fixed"
Theorem f06_for_calldata_fixed_matches_python_oracle:
  ^(#term f06_for_calldata_fixed) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "f06_for_calldata_fixed")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation f06_for_calldata_fixed))) >> EVAL_TAC
QED

(* a row of a 2-D local, a subscript iterable: its shape comes from its type (was iterated as a DynArray). *)
val f50_for_subscript_row = memoryStoreWitnessLib.evaluate fixture_root "f50_for_subscript_row"
Theorem f50_for_subscript_row_matches_python_oracle:
  ^(#term f50_for_subscript_row) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "f50_for_subscript_row")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation f50_for_subscript_row))) >> EVAL_TAC
QED

(* a struct field of a storage struct, a nested place: its location comes
   from the compiled place (was iterated as a memory DynArray at 0). *)
val f38_for_storage_struct_field_arr_set = memoryStoreWitnessLib.evaluate fixture_root "f38_for_storage_struct_field_arr_set"
Theorem f38_for_storage_struct_field_arr_set_matches_python_oracle:
  ^(#term f38_for_storage_struct_field_arr_set) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "f38_for_storage_struct_field_arr_set")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation f38_for_storage_struct_field_arr_set))) >> EVAL_TAC
QED
