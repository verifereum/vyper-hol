Theory lowerDloadGasProducer
Ancestors
  lowerDloadCoverageInvariant lowerDloadOpaqueExecution
  lowerDloadOwnership lowerDloadPairedBoundary lowerDloadFrameCertificate
  lowerDloadSharedState lowerDloadOperand ptrDiscipline venomExecSemantics venomState venomInst
  finite_map

Theorem ld_gas_backward:
  i.inst_opcode = GAS /\ s.vs_gas_readings = t.vs_gas_readings /\
  step_inst ft CT i t = OK t' ==>
  ?out w rest s'. i.inst_outputs = [out] /\
    step_inst fs CS i s = OK s' /\
    s' = update_var out w (s with vs_gas_readings := rest) /\
    t' = update_var out w (t with vs_gas_readings := rest)
Proof
  strip_tac >>
  `step_inst_base i t = OK t'` by
    (qpat_x_assum `step_inst ft _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke]) >>
  qpat_x_assum `step_inst ft _ _ _ = _` kall_tac >>
  gvs[step_inst_base_def, exec_gas_def, AllCaseEqs()] >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_gas_def]
  >- (qexistsl_tac [`0w`, `[]`] >>
      `s with vs_gas_readings := [] = s` by simp[venom_state_component_equality] >>
      `t with vs_gas_readings := [] = t` by simp[venom_state_component_equality] >>
      simp[]) >>
  metis_tac[]
QED

Theorem ld_gas_out_taint[local]:
  i.inst_opcode = GAS ==> out_taint tn i s = {}
Proof
  strip_tac >> simp[out_taint_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[]
  >- (Cases_on `eval_operand h s` >> simp[]) >>
  Cases_on `t'` >> simp[] >>
  Cases_on `eval_operand h s` >> simp[]
QED

Theorem ld_gas_frame_data_backward:
  i.inst_opcode = GAS /\ s.vs_gas_readings = t.vs_gas_readings /\
  ld_frame_data V U E L H AP BP AG BH tn un s t /\
  step_inst ft CT i t = OK t' ==>
  ?s'. step_inst fs CS i s = OK s' /\
    s'.vs_gas_readings = t'.vs_gas_readings /\
    ld_frame_data V U E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >> drule_all ld_gas_backward >>
  disch_then (qspecl_then [`fs`, `CS`] strip_assume_tac) >>
  qexists_tac `s'` >> simp[] >> gvs[] >>
  fs[ld_frame_data_def] >>
  simp[ld_frame_data_def, ld_step_prov_def, ld_out_prov_def] >>
  conj_tac
  >- fs[ld_frame_embedding_def, update_var_def] >>
  conj_tac
  >- (irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  conj_tac
  >- (irule ld_owned_vars_update_supported >>
      qexistsl_tac [`{}`, `{}`, `tn`, `un`] >>
      simp[step_taint_def, ld_gas_out_taint, ld_owned_value_def, ld_mask_word_def] >>
      fs[ld_owned_vars_def, lookup_var_def]) >>
  conj_tac
  >- (simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      fs[lookup_var_def] >> metis_tac[]) >>
  fs[ld_shared_state_def, update_var_def, step_taint_def,
     adopt_reset_def, store_taint_def, imm_taint_def]
QED
