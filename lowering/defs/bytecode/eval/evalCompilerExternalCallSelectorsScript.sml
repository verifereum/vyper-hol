(* Independent checked-frontend bytecode witnesses for interface constructors and call-site selectors. *)
Theory evalCompilerExternalCallSelectors
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../external-calls"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../external-calls/oracle"

val c03_iface_address_attr = memoryStoreWitnessLib.evaluate fixture_root "c03_iface_address_attr"
Theorem c03_iface_address_attr_matches_python_oracle:
  ^(#term c03_iface_address_attr) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "c03_iface_address_attr")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c03_iface_address_attr))) >> EVAL_TAC
QED
