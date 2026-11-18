(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCp03ProxyRof
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

val cp03_proxy_rof = memoryStoreWitnessLib.evaluate fixture_root "cp03_proxy_rof"
Theorem cp03_proxy_rof_matches_python_oracle:
  ^(#term cp03_proxy_rof) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cp03_proxy_rof")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cp03_proxy_rof))) >> EVAL_TAC
QED
