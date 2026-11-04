(* Production-checker normal forms for the fixed raw_call positive controls. *)
Theory vyperRawCallDataAcceptEval
Ancestors
  vyperRawCallDataFixtures
Libs
  vyperCheckContractLib

val raw_data_check_conv =
  REWRITE_CONV [raw_data_modules_def, raw_empty_modules_def, raw_data_flags_def]
  THENC vyperCheckContractLib.check_contract_conv;

(* Select the concrete right side, rejecting non-acceptance before exporting
   the equation. The proofs below independently check each equation. *)
fun accepted_result tm = let
  val answer = rhs (concl (raw_data_check_conv tm))
in
  if optionSyntax.is_some answer then answer
  else raise Fail "raw_call positive control was not accepted"
end;

Theorem raw_data_dynamic_deploy_eval:
  check_contract T [] (0w : address)
    (raw_data_modules (BaseT (BytesT (Dynamic 32)))) =
  ^(accepted_result ``check_contract T [] (0w : address)
    (raw_data_modules (BaseT (BytesT (Dynamic 32))))``)
Proof
  CONV_TAC (LAND_CONV raw_data_check_conv) >> REFL_TAC
QED

Theorem raw_data_dynamic_runtime_eval:
  check_contract F [] (0w : address)
    (raw_data_modules (BaseT (BytesT (Dynamic 32)))) =
  ^(accepted_result ``check_contract F [] (0w : address)
    (raw_data_modules (BaseT (BytesT (Dynamic 32))))``)
Proof
  CONV_TAC (LAND_CONV raw_data_check_conv) >> REFL_TAC
QED

Theorem raw_data_empty_deploy_eval:
  check_contract T [] (0w : address) raw_empty_modules =
  ^(accepted_result ``check_contract T [] (0w : address) raw_empty_modules``)
Proof
  CONV_TAC (LAND_CONV raw_data_check_conv) >> REFL_TAC
QED

Theorem raw_data_empty_runtime_eval:
  check_contract F [] (0w : address) raw_empty_modules =
  ^(accepted_result ``check_contract F [] (0w : address) raw_empty_modules``)
Proof
  CONV_TAC (LAND_CONV raw_data_check_conv) >> REFL_TAC
QED
