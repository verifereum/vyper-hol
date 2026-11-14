Theory o1CodeEndDftTransport
Ancestors
  dftGasInvResidualTrace gasOracleReplay dftGasInvMemoryObservation dftGasSimInvariant
  o1LabelFlowLateDft o1ContractDft codegenSymRel
  dftGasOracleDefs dftRunRel venomExecSemantics venomInstProofs1
  o1PassContract unitShapeDefs venomState contextCodegenRel venomExecProps
  dftGasInvCrossingProbe list dftContractGas dftGasOracleFromList
  dftGasOracleToList dftGasOracleSim dftGasOracleInv o1DftStageSim
  o1DftStageSsa venomPassSchedule venomRetProps stackPlanGen
  contextRawReachable unitMemInv venomInst dftCorrectnessFinal

Theorem code_end_ev_reachable_labels[local]:
  !orc initial ctx p d fn inst t.
    ev_reachable orc initial ctx p d fn inst t ==>
    t.vs_labels = initial.vs_labels
Proof
  ho_match_mp_tac ev_reachable_ind >> rpt strip_tac >>
  gvs[enters_block_def]
  >- (drule eval_phis_preserves_labels >> gvs[])
  >- (drule ev_step_labels >> gvs[])
  >- (drule eval_phis_preserves_labels >> drule ev_step_labels >> gvs[]) >>
  drule eval_phis_preserves_labels >> strip_tac >>
  gvs[setup_callee_def, AllCaseEqs()]
QED

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
  drule_all inv_reachable_memory_observation >> strip_tac >>
  rename1 `MEM source C.ctx_functions` >>
  `o1_fn_shape C source` by metis_tac[o1_ctx_shape_def, EVERY_MEM] >>
  `EVERY label_positions_ok (fn_insts source)` by
    fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >>
  `code_end_var source x` by metis_tac[dft_code_end_var_reflect] >>
  `sS.vs_labels = t.vs_labels` by metis_tac[code_end_ev_reachable_labels] >>
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
  strip_tac >>
  `C'.ctx_functions = MAP dft_fn C.ctx_functions` by
    metis_tac[dft_ctx_functions_map] >>
  drule dft_ctx_block_ids_distinct >> strip_tac >>
  drule_all o1_ctx_shape_wf_functions >> strip_tac >>
  drule_all dft_ctx_wf_functions >> strip_tac >>
  mp_tac (Q.INST [`ctx:venom_context` |-> `C'`, `s:venom_state` |-> `vs'`]
    gas_oracle_from_list) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.INST [`ctx:venom_context` |-> `C`, `s:venom_state` |-> `vs'`]
    gas_oracle_to_list) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_context _ C (vs' with vs_gas_readings := rds)` >>
  qexists_tac `vs' with vs_gas_readings := rds` >>
  conj_tac >- simp[gas_variant_def, venom_state_component_equality] >>
  conj_tac
  >- (rw[ctx_sim_fuel_def] >> irule gas_dft_dead_result >>
      simp[run_context_not_ok, o1_ctx_shape_run_context_no_intret] >>
      qexistsl [`ev_context orc fuel C vs'`, `ev_context orc fuel C' vs'`] >>
      simp[] >> irule dft_ev_context_sim >> simp[] >>
      metis_tac[gas_res_rel_terminates]) >>
  strip_tac >> conj_tac
  >- suspend "lowered" >>
  `code_end_offset_ok
    (\ctx fn inst t. ?p d. ev_reachable orc vs' ctx p d fn inst t) C` by
    (rw[code_end_offset_ok_def] >>
     first_x_assum drule >> strip_tac >>
     fs[code_end_offset_ok_def] >>
     first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all dft_ev_code_end_offset_ok >>
  simp[code_end_offset_ok_def] >> strip_tac >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum (qspecl_then
    [`fn`, `inst`, `vs with vs_gas_readings := vs'.vs_gas_readings`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Resume dft_ctx_code_end_sim_gas[lowered]:
  qpat_x_assum `o1_lowered_inv C _` mp_tac >>
  rw[o1_lowered_inv_def] >> qexists_tac `eom` >>
  conj_tac >- gvs[max_live_eom_def, collect_fn_eoms_dft] >>
  gvs[mem_inv_raw_reachable] >>
  `!p d fn inst t. ev_reachable orc vs' C p d fn inst t ==>
     static_mem_ok eom C fn inst t` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `!p d fn inst t. ev_reachable orc vs' C' p d fn inst t ==>
     static_mem_ok eom C' fn inst t` by
    (mp_tac (Q.INST [`s:venom_state` |-> `vs'`] dft_ev_lowered_inv) >>
     simp[] >> impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  conj_tac
  >- (simp[lookup_function_map, dft_fn_entry_label] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  first_x_assum drule >> simp[]
QED
Finalise dft_ctx_code_end_sim_gas

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
      disch_then (qspec_then `D` strip_assume_tac) >>
      qexists_tac `vs` >> simp[o1_fn_passes_def] >> rpt strip_tac >>
      `o1_lowered_inv C' vs' /\ code_end_offset_ok (raw_reachable vs') C'` by
        metis_tac[] >>
      simp[] >> irule dft_stage_wf_ssa >> metis_tac[]) >>
  qexists_tac `vs'` >> simp[gas_variant_refl]
QED
