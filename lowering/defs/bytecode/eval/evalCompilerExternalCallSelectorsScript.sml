(* Independent checked-frontend bytecode witnesses for interface constructors and call-site selectors. *)
Theory evalCompilerExternalCallSelectors
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../external-calls"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../external-calls/oracle"

val i15_iface_ret_iface_direct = memoryStoreWitnessLib.evaluate fixture_root "i15_iface_ret_iface_direct"
Theorem i15_iface_ret_iface_direct_matches_python_oracle:
  ^(#term i15_iface_ret_iface_direct) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "i15_iface_ret_iface_direct")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation i15_iface_ret_iface_direct))) >> EVAL_TAC
QED

val i09_iface_ret_iface = memoryStoreWitnessLib.evaluate fixture_root "i09_iface_ret_iface"
Theorem i09_iface_ret_iface_matches_python_oracle:
  ^(#term i09_iface_ret_iface) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "i09_iface_ret_iface")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation i09_iface_ret_iface))) >> EVAL_TAC
QED

val c03_iface_address_attr = memoryStoreWitnessLib.evaluate fixture_root "c03_iface_address_attr"
Theorem c03_iface_address_attr_matches_python_oracle:
  ^(#term c03_iface_address_attr) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "c03_iface_address_attr")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c03_iface_address_attr))) >> EVAL_TAC
QED

val i02_iface_default_param = memoryStoreWitnessLib.evaluate fixture_root "i02_iface_default_param"
Theorem i02_iface_default_param_matches_python_oracle:
  ^(#term i02_iface_default_param) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "i02_iface_default_param")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation i02_iface_default_param))) >> EVAL_TAC
QED

val i03_two_ifaces_same_name = memoryStoreWitnessLib.evaluate fixture_root "i03_two_ifaces_same_name"
Theorem i03_two_ifaces_same_name_matches_python_oracle:
  ^(#term i03_two_ifaces_same_name) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "i03_two_ifaces_same_name")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation i03_two_ifaces_same_name))) >> EVAL_TAC
QED

val i13_ext_fn_before_iface = memoryStoreWitnessLib.evaluate fixture_root "i13_ext_fn_before_iface"
Theorem i13_ext_fn_before_iface_matches_python_oracle:
  ^(#term i13_ext_fn_before_iface) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "i13_ext_fn_before_iface")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation i13_ext_fn_before_iface))) >> EVAL_TAC
QED
