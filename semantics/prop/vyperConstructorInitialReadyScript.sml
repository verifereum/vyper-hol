(* Checked constants establish constructor readiness independently of trace. *)
Theory vyperConstructorInitialReady
Ancestors
  vyperTypeDeploymentMachine vyperTypeContractSoundness
  vyperTypeInvariants vyperTypeSystem vyperInterpreter vyperState
  vyperTypeEntryReadiness vyperTypeInitialState vyperContext

Theorem checked_constructor_initial_state_ready:
  check_contract T layouts target mods = SOME deploy_art /\
  check_contract F layouts target mods = SOME runtime_art /\
  ALOOKUP sources target = SOME mods /\ tx.target = target /\
  cx = (initial_evaluation_context sources layouts tx NONE with in_deploy := T) /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  machine_well_typed (am with immutables updated_by CONS (target,imms)) /\
  checked_deployment_constants_ready cx
    (am with immutables updated_by CONS (target,imms)) target mods /\
  evaluate_all_constants cx
    (am with immutables updated_by CONS (target,imms)) target mods = SOME am_c ==>
  state_well_typed
    (initial_state am_c [FEMPTY] with
      <|outcomes := orc; requests := rqs; gas_obs := gobs; storage_trace := obs|>) /\
  accounts_well_typed am_c.accounts /\
  env_immutables_consistent (artifact_env deploy_art mods NONE) cx
    (initial_state am_c [FEMPTY] with
      <|outcomes := orc; requests := rqs; gas_obs := gobs; storage_trace := obs|>)
Proof
  strip_tac >>
  `machine_well_typed am_c` by
    (gvs[checked_deployment_constants_ready_def] >>
     drule_all evaluate_all_constants_preserves_accounts >>
     gvs[machine_well_typed_def, deployment_constants_output_typed_def]) >>
  `env_immutables_consistent (artifact_env deploy_art mods NONE) cx
    (initial_state am_c [FEMPTY] with
      <|outcomes := orc; requests := rqs; gas_obs := gobs|>)` by
    (irule checked_deployment_constants_establish_initial_env_immutables_consistent >>
     metis_tac[]) >>
  conj_tac
  >- gvs[machine_well_typed_def, state_well_typed_def,
         initial_state_def, scope_well_typed_def] >>
  conj_tac >- gvs[machine_well_typed_def] >>
  irule (iffLR env_immutables_consistent_immutables_cong) >>
  goal_assum (drule_at Any) >> simp[]
QED
