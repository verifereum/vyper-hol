(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltins2
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../create-builtins"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../create-builtins/oracle"

val cp02_proxy_value_salt = memoryStoreWitnessLib.evaluate fixture_root "cp02_proxy_value_salt"
Theorem cp02_proxy_value_salt_matches_python_oracle:
  ^(#term cp02_proxy_value_salt) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cp02_proxy_value_salt")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cp02_proxy_value_salt))) >> EVAL_TAC
QED

val cp03_proxy_rof = memoryStoreWitnessLib.evaluate fixture_root "cp03_proxy_rof"
Theorem cp03_proxy_rof_matches_python_oracle:
  ^(#term cp03_proxy_rof) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cp03_proxy_rof")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cp03_proxy_rof))) >> EVAL_TAC
QED

val cp04_forwarder_alias = memoryStoreWitnessLib.evaluate fixture_root "cp04_forwarder_alias"
Theorem cp04_forwarder_alias_matches_python_oracle:
  ^(#term cp04_forwarder_alias) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cp04_forwarder_alias")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cp04_forwarder_alias))) >> EVAL_TAC
QED

val cb04_blueprint_offset_salt_value = memoryStoreWitnessLib.evaluate fixture_root "cb04_blueprint_offset_salt_value"
Theorem cb04_blueprint_offset_salt_value_matches_python_oracle:
  ^(#term cb04_blueprint_offset_salt_value) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb04_blueprint_offset_salt_value")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb04_blueprint_offset_salt_value))) >> EVAL_TAC
QED

val cb03_blueprint_rawargs = memoryStoreWitnessLib.evaluate fixture_root "cb03_blueprint_rawargs"
Theorem cb03_blueprint_rawargs_matches_python_oracle:
  ^(#term cb03_blueprint_rawargs) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb03_blueprint_rawargs")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb03_blueprint_rawargs))) >> EVAL_TAC
QED

val cb08_blueprint_runtime_offset = memoryStoreWitnessLib.evaluate fixture_root "cb08_blueprint_runtime_offset"
Theorem cb08_blueprint_runtime_offset_matches_python_oracle:
  ^(#term cb08_blueprint_runtime_offset) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb08_blueprint_runtime_offset")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb08_blueprint_runtime_offset))) >> EVAL_TAC
QED

val cb09_blueprint_folded_offset = memoryStoreWitnessLib.evaluate fixture_root "cb09_blueprint_folded_offset"
Theorem cb09_blueprint_folded_offset_matches_python_oracle:
  ^(#term cb09_blueprint_folded_offset) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb09_blueprint_folded_offset")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb09_blueprint_folded_offset))) >> EVAL_TAC
QED

val cb10_blueprint_flag_offset = memoryStoreWitnessLib.evaluate fixture_root "cb10_blueprint_flag_offset"
Theorem cb10_blueprint_flag_offset_matches_python_oracle:
  ^(#term cb10_blueprint_flag_offset) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb10_blueprint_flag_offset")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb10_blueprint_flag_offset))) >> EVAL_TAC
QED

val cb11_blueprint_folded_wei_offset = memoryStoreWitnessLib.evaluate fixture_root "cb11_blueprint_folded_wei_offset"
Theorem cb11_blueprint_folded_wei_offset_matches_python_oracle:
  ^(#term cb11_blueprint_folded_wei_offset) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb11_blueprint_folded_wei_offset")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb11_blueprint_folded_wei_offset))) >> EVAL_TAC
QED

val cb12_blueprint_unsafe_offset = memoryStoreWitnessLib.evaluate fixture_root "cb12_blueprint_unsafe_offset"
Theorem cb12_blueprint_unsafe_offset_matches_python_oracle:
  ^(#term cb12_blueprint_unsafe_offset) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb12_blueprint_unsafe_offset")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb12_blueprint_unsafe_offset))) >> EVAL_TAC
QED
