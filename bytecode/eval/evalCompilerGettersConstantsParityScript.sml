(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParity
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../getters-constants/oracle"

val g01_pub_uint256 = memoryStoreWitnessLib.evaluate fixture_root "g01_pub_uint256"
Theorem g01_pub_uint256_matches_python_oracle:
  ^(#term g01_pub_uint256) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g01_pub_uint256")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g01_pub_uint256))) >> EVAL_TAC
QED

val g13_pub_dynarray = memoryStoreWitnessLib.evaluate fixture_root "g13_pub_dynarray"
Theorem g13_pub_dynarray_matches_python_oracle:
  ^(#term g13_pub_dynarray) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g13_pub_dynarray")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g13_pub_dynarray))) >> EVAL_TAC
QED

val g15_pub_hashmap = memoryStoreWitnessLib.evaluate fixture_root "g15_pub_hashmap"
Theorem g15_pub_hashmap_matches_python_oracle:
  ^(#term g15_pub_hashmap) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g15_pub_hashmap")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g15_pub_hashmap))) >> EVAL_TAC
QED

val g25_pub_with_external = memoryStoreWitnessLib.evaluate fixture_root "g25_pub_with_external"
Theorem g25_pub_with_external_matches_python_oracle:
  ^(#term g25_pub_with_external) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g25_pub_with_external")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g25_pub_with_external))) >> EVAL_TAC
QED

val g26_pub_with_default = memoryStoreWitnessLib.evaluate fixture_root "g26_pub_with_default"
Theorem g26_pub_with_default_matches_python_oracle:
  ^(#term g26_pub_with_default) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g26_pub_with_default")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g26_pub_with_default))) >> EVAL_TAC
QED

val c02_const_string = memoryStoreWitnessLib.evaluate fixture_root "c02_const_string"
Theorem c02_const_string_matches_python_oracle:
  ^(#term c02_const_string) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c02_const_string")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c02_const_string))) >> EVAL_TAC
QED

val c05_const_address = memoryStoreWitnessLib.evaluate fixture_root "c05_const_address"
Theorem c05_const_address_matches_python_oracle:
  ^(#term c05_const_address) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c05_const_address")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c05_const_address))) >> EVAL_TAC
QED

val c09_const_bytes32 = memoryStoreWitnessLib.evaluate fixture_root "c09_const_bytes32"
Theorem c09_const_bytes32_matches_python_oracle:
  ^(#term c09_const_bytes32) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c09_const_bytes32")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c09_const_bytes32))) >> EVAL_TAC
QED

val c11_const_decimal = memoryStoreWitnessLib.evaluate fixture_root "c11_const_decimal"
Theorem c11_const_decimal_matches_python_oracle:
  ^(#term c11_const_decimal) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c11_const_decimal")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c11_const_decimal))) >> EVAL_TAC
QED

val c14_pub_const_string = memoryStoreWitnessLib.evaluate fixture_root "c14_pub_const_string"
Theorem c14_pub_const_string_matches_python_oracle:
  ^(#term c14_pub_const_string) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c14_pub_const_string")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c14_pub_const_string))) >> EVAL_TAC
QED

val c26_const_array_local = memoryStoreWitnessLib.evaluate fixture_root "c26_const_array_local"
Theorem c26_const_array_local_matches_python_oracle:
  ^(#term c26_const_array_local) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c26_const_array_local")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c26_const_array_local))) >> EVAL_TAC
QED

val i13_public_immut_address = memoryStoreWitnessLib.evaluate fixture_root "i13_public_immut_address"
Theorem i13_public_immut_address_matches_python_oracle:
  ^(#term i13_public_immut_address) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "i13_public_immut_address")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation i13_public_immut_address))) >> EVAL_TAC
QED

val g17_pub_hashmap_nested = memoryStoreWitnessLib.evaluate fixture_root "g17_pub_hashmap_nested"
Theorem g17_pub_hashmap_nested_matches_python_oracle:
  ^(#term g17_pub_hashmap_nested) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g17_pub_hashmap_nested")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g17_pub_hashmap_nested))) >> EVAL_TAC
QED

val g21_pub_hashmap_array_val = memoryStoreWitnessLib.evaluate fixture_root "g21_pub_hashmap_array_val"
Theorem g21_pub_hashmap_array_val_matches_python_oracle:
  ^(#term g21_pub_hashmap_array_val) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g21_pub_hashmap_array_val")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g21_pub_hashmap_array_val))) >> EVAL_TAC
QED

val g23_pub_transient_hashmap = memoryStoreWitnessLib.evaluate fixture_root "g23_pub_transient_hashmap"
Theorem g23_pub_transient_hashmap_matches_python_oracle:
  ^(#term g23_pub_transient_hashmap) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g23_pub_transient_hashmap")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g23_pub_transient_hashmap))) >> EVAL_TAC
QED

val g24_pub_2d_array = memoryStoreWitnessLib.evaluate fixture_root "g24_pub_2d_array"
Theorem g24_pub_2d_array_matches_python_oracle:
  ^(#term g24_pub_2d_array) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g24_pub_2d_array")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g24_pub_2d_array))) >> EVAL_TAC
QED

val g31_pub_hashmap_dynarray_val = memoryStoreWitnessLib.evaluate fixture_root "g31_pub_hashmap_dynarray_val"
Theorem g31_pub_hashmap_dynarray_val_matches_python_oracle:
  ^(#term g31_pub_hashmap_dynarray_val) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g31_pub_hashmap_dynarray_val")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g31_pub_hashmap_dynarray_val))) >> EVAL_TAC
QED

val c_sha256_initializer = memoryStoreWitnessLib.evaluate fixture_root "c_sha256_initializer"
Theorem c_sha256_initializer_matches_python_oracle:
  ^(#term c_sha256_initializer) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c_sha256_initializer")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c_sha256_initializer))) >> EVAL_TAC
QED
