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

val i15_iface_ret_iface_direct = memoryStoreWitnessLib.evaluate fixture_root "i15_iface_ret_iface_direct"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "i15_iface_ret_iface_direct" i15_iface_ret_iface_direct

val i09_iface_ret_iface = memoryStoreWitnessLib.evaluate fixture_root "i09_iface_ret_iface"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "i09_iface_ret_iface" i09_iface_ret_iface

val c03_iface_address_attr = memoryStoreWitnessLib.evaluate fixture_root "c03_iface_address_attr"
Theorem c03_iface_address_attr_matches_python_oracle:
  ^(#term c03_iface_address_attr) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "c03_iface_address_attr")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c03_iface_address_attr))) >> EVAL_TAC
QED

val i02_iface_default_param = memoryStoreWitnessLib.evaluate fixture_root "i02_iface_default_param"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "i02_iface_default_param" i02_iface_default_param

val i03_two_ifaces_same_name = memoryStoreWitnessLib.evaluate fixture_root "i03_two_ifaces_same_name"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "i03_two_ifaces_same_name" i03_two_ifaces_same_name

val i13_ext_fn_before_iface = memoryStoreWitnessLib.evaluate fixture_root "i13_ext_fn_before_iface"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "i13_ext_fn_before_iface" i13_ext_fn_before_iface
