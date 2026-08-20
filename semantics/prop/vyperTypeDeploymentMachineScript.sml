(*
 * Machine-typing establishment for checked contract deployment.
 *
 * This theory composes typed initial immutables, deployment constants, and
 * constructor execution.  It is downstream of ordinary external-call machine
 * preservation so deployment and call reasoning remain separate.
 *
 * TOP-LEVEL:
 * - load_contract_establishes_machine_well_typed
 *)

Theory vyperTypeDeploymentMachine
Ancestors
  vyperTypeEntryReadiness vyperTypeContractSoundness
  vyperTypeExternalCallMachine

val _ = Parse.hide "body";

val _ = export_theory();
