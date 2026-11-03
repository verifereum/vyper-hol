Theory vyperRawCallDataReject
Ancestors
  vyperRawCallDataFixtures vyperRawCallDataDomain
Libs
  vyperCheckContractLib

val raw_data_check_contract_conv =
  REWRITE_CONV [raw_data_modules_def, raw_empty_modules_def, raw_data_flags_def]
  THENC vyperCheckContractLib.check_contract_conv;

(* WHY THIS IS TRUE: The bytes32 argument is an assignable, well-formed type,
   so rejection is specifically caused by the ordinary raw-call data rule,
   not an invalid declaration. raw_call_typed_data_dynamic rules out that
   expression in any environment. Both production checker modes must reject
   the complete contract, including the deploy reachability treatment. *)
Theorem raw_call_fixed_data_contract_rejected:
  !in_deploy.
    check_contract in_deploy [] (0w : address)
      (raw_data_modules (BaseT (BytesT (Fixed 32)))) = NONE
Proof
  Cases >> CONV_TAC (LAND_CONV
    raw_data_check_contract_conv) >> REFL_TAC
QED
