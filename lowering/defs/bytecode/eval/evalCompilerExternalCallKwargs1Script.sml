(* Independent checked-frontend bytecode witnesses for the keyword operands
   of extcall/staticcall (value=, gas=, default_return_value=,
   skip_contract_check=) and for send with and without gas=.
   Half 1 of evalCompilerExternalCallKwargs: e40_extcall_gas,
   e43_extcall_all_kwargs, e44_skip_contract_check, s02_send_gas,
   e29_default_ret_skip. *)
Theory evalCompilerExternalCallKwargs1
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../external-calls"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../external-calls/oracle"

val e40_extcall_gas = memoryStoreWitnessLib.evaluate fixture_root "e40_extcall_gas"
Theorem e40_extcall_gas_matches_python_oracle:
  ^(#term e40_extcall_gas) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e40_extcall_gas")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e40_extcall_gas))) >> EVAL_TAC
QED

val e43_extcall_all_kwargs = memoryStoreWitnessLib.evaluate fixture_root "e43_extcall_all_kwargs"
Theorem e43_extcall_all_kwargs_matches_python_oracle:
  ^(#term e43_extcall_all_kwargs) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e43_extcall_all_kwargs")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e43_extcall_all_kwargs))) >> EVAL_TAC
QED

val e44_skip_contract_check = memoryStoreWitnessLib.evaluate fixture_root "e44_skip_contract_check"
Theorem e44_skip_contract_check_matches_python_oracle:
  ^(#term e44_skip_contract_check) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e44_skip_contract_check")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e44_skip_contract_check))) >> EVAL_TAC
QED

val s02_send_gas = memoryStoreWitnessLib.evaluate fixture_root "s02_send_gas"
Theorem s02_send_gas_matches_python_oracle:
  ^(#term s02_send_gas) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "s02_send_gas")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation s02_send_gas))) >> EVAL_TAC
QED

val e29_default_ret_skip = memoryStoreWitnessLib.evaluate fixture_root "e29_default_ret_skip"
Theorem e29_default_ret_skip_matches_python_oracle:
  ^(#term e29_default_ret_skip) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e29_default_ret_skip")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e29_default_ret_skip))) >> EVAL_TAC
QED
