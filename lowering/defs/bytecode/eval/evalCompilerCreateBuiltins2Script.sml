(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltins2
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../create-builtins"]
val () = supportedEvalLib.configure ()
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

