Theory o1CodeEndDftTransport
Ancestors
  dftGasInvResidualTrace gasOracleReplay dftGasInvMemoryObservation
  o1LabelFlowLateDft o1ContractDft codegenSymRel
  dftGasOracleDefs dftRunRel venomExecSemantics venomInstProofs1
  o1PassContract unitShapeDefs venomState contextCodegenRel venomExecProps
  dftGasInvCrossingProbe list dftContractGas dftGasOracleFromList
  dftGasOracleToList dftGasOracleSim dftGasOracleInv o1DftStageSim
  o1DftStageSsa venomPassSchedule venomRetProps stackPlanGen
  contextRawReachable unitMemInv venomInst dftCorrectnessFinal

Theorem dft_ev_code_end_offset_ok[local]:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_run_state_ok initial /\
  code_end_offset_ok (\ctx fn inst t. ?p d. ev_reachable orc initial ctx p d fn inst t) C ==>
  code_end_offset_ok (\ctx fn inst t. ?p d. ev_reachable orc initial ctx p d fn inst t) C'
Proof
  strip_tac >> rw[code_end_offset_ok_def] >>
  `inv_memory_observation inst.inst_opcode` by simp[inv_memory_observation_def] >>
  drule_all inv_reachable_memory_observation >>
  disch_then (qx_choosel_then
    [`source`,`source_state`,`source_block`,`target_block`] strip_assume_tac) >>
  `o1_fn_shape C source` by metis_tac[o1_ctx_shape_def, EVERY_MEM] >>
  `EVERY label_positions_ok (fn_insts source)` by
    fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >>
  `code_end_var source x` by metis_tac[dft_code_end_var_reflect] >>
  `source_state.vs_labels = t.vs_labels` by metis_tac[ev_reachable_labels] >>
  fs[code_end_offset_ok_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[MEM]
QED

Theorem dft_ctx_code_end_sim_gas[local]:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\ ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim_fuel I D C C' vs vs' /\
    (o1_lowered_inv C vs /\ code_end_offset_ok (raw_reachable vs) C ==>
     o1_lowered_inv C' vs' /\ code_end_offset_ok (raw_reachable vs') C')
Proof
  strip_tac >> drule_all dft_ctx_sim_gas_oracle >>
  disch_then (qspec_then `D`
    (qx_choosel_then [`source_state`,`orc`] strip_assume_tac)) >>
  qexists_tac `source_state` >> simp[] >> strip_tac >>
  `code_end_offset_ok
    (\ctx fn inst t. ?p d. ev_reachable orc vs' ctx p d fn inst t) C` by
    (rw[code_end_offset_ok_def] >>
     first_x_assum drule >> strip_tac >>
     fs[code_end_offset_ok_def] >>
     first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all dft_ev_code_end_offset_ok >>
  simp[code_end_offset_ok_def] >> strip_tac >> rpt strip_tac >>
  rename1 `raw_reachable vs' C' fn inst target_state` >>
  first_x_assum drule >> strip_tac >>
  first_x_assum (qspecl_then
    [`fn`, `inst`, `target_state with vs_gas_readings := vs'.vs_gas_readings`] mp_tac) >>
  simp[] >> metis_tac[]
QED


Theorem dft_code_end_stage_contract_gas:
  o1_stage_contract_gas rpolicy D (EL 7 o1_fn_passes)
    (o1_walk_view rpolicy 7) (o1_pre 7)
    (\C s. o1_inv D 7 C s /\ code_end_offset_ok (raw_reachable s) C)
    (\C s. o1_inv D 8 C s /\ code_end_offset_ok (raw_reachable s) C)
Proof
  simp[o1_stage_contract_gas_def, o1_inv_def, o1_ssa_inv_def, pass_fuel_def] >>
  rpt strip_tac >> rename1 `o1_run_state_ok vs'` >>
  Cases_on `EVERY wf_ssa C.ctx_functions`
  >- (`ctx_pass_stage rpolicy (CFP_Simple VP_DFT) (o1_walk_view rpolicy 7) C C'` by
        gvs[o1_fn_passes_def] >>
      drule_all dft_stage_fn_rel >> strip_tac >>
      drule ctx_pass_stage_dft >> strip_tac >>
      `ctx_labels_bound C vs'.vs_labels` by
        (irule dft_ctx_labels_bound >> gvs[o1_run_state_ok_def]) >>
      drule_all dft_ctx_code_end_sim_gas >>
      disch_then (qspec_then `D` (qx_choose_then `source_state` strip_assume_tac)) >>
      qexists_tac `source_state` >> simp[o1_fn_passes_def] >> rpt strip_tac >>
      `o1_lowered_inv C' vs' /\ code_end_offset_ok (raw_reachable vs') C'` by
        metis_tac[] >>
      simp[] >> irule dft_stage_wf_ssa >> metis_tac[]) >>
  qexists_tac `vs'` >> simp[gas_variant_refl]
QED
