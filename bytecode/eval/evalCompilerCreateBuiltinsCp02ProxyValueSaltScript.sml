(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCp02ProxyValueSalt
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
