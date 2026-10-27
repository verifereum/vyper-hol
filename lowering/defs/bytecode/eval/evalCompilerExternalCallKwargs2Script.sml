(* Independent checked-frontend bytecode witnesses for the keyword operands
   of extcall/staticcall (value=, gas=, default_return_value=,
   skip_contract_check=) and for send with and without gas=.
   Half 2 of evalCompilerExternalCallKwargs: e41_staticcall_gas,
   e42_extcall_gas_value_order, e45_default_ret_ifexp, s01_send, e19_gas_kw. *)
Theory evalCompilerExternalCallKwargs2
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../external-calls/oracle/e41_staticcall_gas.json",
   "../external-calls/oracle/e41_staticcall_gas.hex",
   "../external-calls/oracle/e42_extcall_gas_value_order.json",
   "../external-calls/oracle/e42_extcall_gas_value_order.hex",
   "../external-calls/oracle/e45_default_ret_ifexp.json",
   "../external-calls/oracle/e45_default_ret_ifexp.hex",
   "../external-calls/oracle/s01_send.json",
   "../external-calls/oracle/s01_send.hex",
   "../external-calls/oracle/e19_gas_kw.json",
   "../external-calls/oracle/e19_gas_kw.hex"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../external-calls/oracle"

val e41_staticcall_gas = memoryStoreWitnessLib.evaluate fixture_root "e41_staticcall_gas"
Theorem e41_staticcall_gas_matches_python_oracle:
  ^(#term e41_staticcall_gas) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e41_staticcall_gas")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e41_staticcall_gas))) >> EVAL_TAC
QED

val e42_extcall_gas_value_order = memoryStoreWitnessLib.evaluate fixture_root "e42_extcall_gas_value_order"
Theorem e42_extcall_gas_value_order_matches_python_oracle:
  ^(#term e42_extcall_gas_value_order) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e42_extcall_gas_value_order")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e42_extcall_gas_value_order))) >> EVAL_TAC
QED

val e45_default_ret_ifexp = memoryStoreWitnessLib.evaluate fixture_root "e45_default_ret_ifexp"
Theorem e45_default_ret_ifexp_matches_python_oracle:
  ^(#term e45_default_ret_ifexp) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e45_default_ret_ifexp")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e45_default_ret_ifexp))) >> EVAL_TAC
QED

val s01_send = memoryStoreWitnessLib.evaluate fixture_root "s01_send"
Theorem s01_send_matches_python_oracle:
  ^(#term s01_send) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "s01_send")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation s01_send))) >> EVAL_TAC
QED

val e19_gas_kw = memoryStoreWitnessLib.evaluate fixture_root "e19_gas_kw"
Theorem e19_gas_kw_matches_python_oracle:
  ^(#term e19_gas_kw) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e19_gas_kw")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e19_gas_kw))) >> EVAL_TAC
QED
