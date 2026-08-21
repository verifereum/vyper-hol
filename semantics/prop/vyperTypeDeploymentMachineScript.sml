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
  vyperContext vyperState vyperInterpreter vyperTypeInvariants
  vyperTypeInitialState vyperTypeEntryReadiness vyperTypeContract
  vyperTypeContractStaticMaps vyperTypeContractContext vyperTypeContractSoundness
  vyperTypeExternalCallMachine

val _ = Parse.hide "body";

(* ===== Deployment machine setup ===== *)

Theorem env_context_consistent_enter_deploy[local]:
  env_context_consistent env cx /\
  fn_sigs_consistent env.fn_sigs (cx with in_deploy := T) /\
  fn_sigs_declared_complete env.fn_sigs (cx with in_deploy := T) ==>
  env_context_consistent env (cx with in_deploy := T)
Proof
  rw[env_context_consistent_def] >>
  gvs[fn_sigs_consistent_def, toplevel_vtypes_complete_def,
      bare_globals_complete_def, bare_global_assignable_complete_def,
      flag_members_complete_def, get_module_code_def, get_tenv_def,
      current_module_def, lookup_var_slot_from_layout_def] >>
  metis_tac[]
QED

Theorem checked_deployment_env_context_consistent:
  check_contract T layouts addr mods = SOME deploy_art /\
  check_contract F layouts addr mods = SOME runtime_art /\
  ALOOKUP sources addr = SOME mods /\ tx.target = addr ==>
  env_context_consistent (artifact_env deploy_art mods NONE)
    (initial_evaluation_context sources layouts tx NONE with in_deploy := T)
Proof
  strip_tac >>
  `env_context_consistent (artifact_env runtime_art mods NONE)
     (initial_evaluation_context sources layouts tx NONE)` by
    (irule check_contract_env_context_consistent_initial_NONE >> simp[]) >>
  `fn_sigs_consistent deploy_art.cta_fn_sigs
     (initial_evaluation_context sources layouts tx NONE with in_deploy := T)` by
    (irule check_contract_fn_sigs_consistent_deploy >> simp[]) >>
  `fn_sigs_declared_complete deploy_art.cta_fn_sigs
     (initial_evaluation_context sources layouts tx NONE with in_deploy := T)` by
    (irule check_contract_fn_sigs_declared_complete_deploy >> simp[]) >>
  `deploy_art.cta_bare_globals = runtime_art.cta_bare_globals /\
   deploy_art.cta_bare_global_assignable = runtime_art.cta_bare_global_assignable /\
   deploy_art.cta_toplevel_vtypes = runtime_art.cta_toplevel_vtypes /\
   deploy_art.cta_flag_members = runtime_art.cta_flag_members` by
    (gvs[check_contract_def] >>
     metis_tac[build_contract_type_artifact_nonsig_mode_irrelevant]) >>
  gvs[env_context_consistent_def, artifact_env_def,
      get_module_code_def, get_tenv_def, current_module_def,
      initial_evaluation_context_def, lookup_var_slot_from_layout_def,
      fn_sigs_consistent_def, fn_sigs_declared_complete_def,
      toplevel_vtypes_complete_def, bare_globals_complete_def,
      bare_global_assignable_complete_def, flag_members_complete_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

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
