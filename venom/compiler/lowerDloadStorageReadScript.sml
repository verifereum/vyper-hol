Theory lowerDloadStorageRead
Ancestors
  lowerDloadSharedState lowerDloadMaskedStorage lowerDloadReadEffects lowerDloadScalarClosure
  lowerDloadOwnership lowerDloadOperand lowerDloadPairedBoundary
  venomExecSemantics venomInst ptrDiscipline list words pred_set

Theorem ld_storage_read_backward:
  MEM i.inst_opcode [SLOAD; TLOAD] /\ ld_shared_state tn un s t /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s' out x y. step_inst fuelS CS i s = OK s' /\ i.inst_outputs = [out] /\
    s' = update_var out x s /\ t' = update_var out y t /\
    ld_mask_word (out_taint tn i s) (out_taint un i t) x y
Proof
  strip_tac >>
  drule ld_shared_state_masks >> strip_tac >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[MEM] >> strip_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[exec_read1_def, AllCaseEqs()] >> strip_tac >>
  gvs[]
  >- (drule ld_shared_sload >>
      disch_then (qspec_then `key` assume_tac) >>
      qexistsl_tac [`sload key s`,`sload key t`] >>
      simp[Once step_inst_non_invoke] >>
      asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
      simp[exec_read1_def, out_taint_def] >>
      gvs[ld_mask_word_def, word_agree_except_def, key_taint_def, SUBSET_DEF] >>
      metis_tac[]) >>
  drule ld_shared_tload >>
  disch_then (qspec_then `key` assume_tac) >>
  qexistsl_tac [`tload key s`,`tload key t`] >>
  simp[Once step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[exec_read1_def, out_taint_def] >>
  gvs[ld_mask_word_def, word_agree_except_def, key_taint_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem ld_owned_storage_read_backward:
  MEM i.inst_opcode [SLOAD; TLOAD] /\ ld_shared_state tn un s t /\
  i.inst_outputs = [out] /\ ld_owned_vars V E AG AH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!op. MEM op i.inst_operands ==> ld_op_prov AG op = NONE /\ op_taint tn op = {}) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_owned_operand_clean >> simp[] >> metis_tac[]) >>
  drule_all ld_storage_read_backward >>
  disch_then (qspecl_then [`fuelS`,`CS`] strip_assume_tac) >> gvs[] >>
  `ld_owned_value E NONE NONE (out_taint tn i s) (out_taint un i t) x y` by
    simp[ld_owned_value_def] >>
  drule_all ld_owned_vars_update >>
  disch_then (qspec_then `out` mp_tac) >>
  simp[ld_step_prov_def, ld_out_prov_def, step_taint_def,
       ld_owned_vars_def, op_taint_def]
QED
