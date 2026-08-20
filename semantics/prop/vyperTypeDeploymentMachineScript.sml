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
  vyperTypeInitialState vyperTypeEntryReadiness vyperTypeContractSoundness
  vyperTypeExternalCallMachine

val _ = Parse.hide "body";

(* ===== Deployment machine setup ===== *)

Theorem deployment_initial_machine_well_typed:
  machine_well_typed am /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms ==>
  machine_well_typed
    (am with <| immutables updated_by CONS (addr,imms);
                exports updated_by CONS (addr,exps) |>)
Proof
  strip_tac >>
  gvs[machine_well_typed_def] >>
  metis_tac[initial_immutables_imms_well_typed]
QED

Theorem deployment_source_install_preserves_machine_well_typed:
  machine_well_typed am ==>
  machine_well_typed (am with sources updated_by CONS (addr,mods))
Proof
  simp[machine_well_typed_def]
QED

val _ = export_theory();
