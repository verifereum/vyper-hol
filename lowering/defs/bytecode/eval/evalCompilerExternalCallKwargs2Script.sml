(* Independent checked-frontend bytecode witnesses for the keyword operands
   of extcall/staticcall (value=, gas=, default_return_value=,
   skip_contract_check=) and for send with and without gas=.
   Half 2 of evalCompilerExternalCallKwargs: e41_staticcall_gas,
   e42_extcall_gas_value_order, e45_default_ret_ifexp, s01_send, e19_gas_kw. *)
Theory evalCompilerExternalCallKwargs2
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../external-calls"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../external-calls/oracle"

val e41_staticcall_gas = memoryStoreWitnessLib.evaluate fixture_root "e41_staticcall_gas"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "e41_staticcall_gas" e41_staticcall_gas

val e42_extcall_gas_value_order = memoryStoreWitnessLib.evaluate fixture_root "e42_extcall_gas_value_order"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "e42_extcall_gas_value_order" e42_extcall_gas_value_order

val e45_default_ret_ifexp = memoryStoreWitnessLib.evaluate fixture_root "e45_default_ret_ifexp"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "e45_default_ret_ifexp" e45_default_ret_ifexp

val s01_send = memoryStoreWitnessLib.evaluate fixture_root "s01_send"
Theorem s01_send_matches_python_oracle:
  ^(#term s01_send) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "s01_send")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation s01_send))) >> EVAL_TAC
QED

val e19_gas_kw = memoryStoreWitnessLib.evaluate fixture_root "e19_gas_kw"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "e19_gas_kw" e19_gas_kw
