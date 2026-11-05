Theory deadStoreElimRegisterSteps
Ancestors
  deadStoreElimPureSteps deadStoreElimLocal deadStoreElimPending
  deadStoreElimLiveness deadStoreElimSafety deadStoreElimDefs
  venomExecSemantics venomState venomEffects venomInst basePtrDefs memLocDefs
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Definition dse_register_opcode_def:
  dse_register_opcode opc <=>
    opc IN {OFFSET; ASSIGN; NOP; PARAM; FMP_PARAM; RETPC_PARAM; INITIAL_FMP; BUMP}
End

Theorem dse_register_write_location:
  dse_register_opcode inst.inst_opcode ==>
  bp_get_write_location bp inst sp = ml_empty
Proof
  simp[dse_register_opcode_def] >> strip_tac >> Cases_on `sp` >>
  simp[bp_get_write_location_def, is_raw_fmp_opcode_def,
       write_effects_def, empty_effects_def]
QED

Theorem dse_register_no_clobber:
  dse_register_opcode inst.inst_opcode /\
  loc.ml_size = SOME n /\ 0 < n ==>
  ~dse_inst_clobbers bp sp loc inst
Proof
  strip_tac >> drule dse_register_write_location >>
  disch_then (qspec_then `sp` assume_tac) >>
  simp[dse_inst_clobbers_def, ml_empty_def, completely_contains_def]
QED

Theorem dse_register_local_step:
  dse_register_opcode inst.inst_opcode /\
  dse_local_agrees sp P s t /\ step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
       dse_local_agrees sp P s1 t1 /\ s1.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `s.vs_params = t.vs_params /\ s.vs_initial_fmp = t.vs_initial_fmp /\
   s.vs_return_pc_token = t.vs_return_pc_token` by
    fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def,
       dse_operational_agrees_def] >>
  Cases_on `inst.inst_opcode = OFFSET`
  >- (gvs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
      drule_all exec_pure2_common_update >> strip_tac >>
      qexists_tac `update_var out w t` >>
      gvs[dse_local_agrees_update_var] >> simp[update_var_def]) >>
  fs[dse_register_opcode_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[dse_local_agrees_update_var, update_var_def]
QED

Theorem dse_register_pending_step:
  dse_register_opcode inst.inst_opcode /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\ s1.vs_allocas = s.vs_allocas ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P s1
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[] >>
  irule dse_pending_at_step >> simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  irule dse_register_no_clobber >> metis_tac[]
QED

Theorem dse_local_agrees_register_step:
  dse_register_opcode inst.inst_opcode /\
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp sp fn bb (SUC s.vs_inst_idx) P s1
Proof
  strip_tac >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  drule_all dse_register_local_step >> strip_tac >>
  qexists_tac `t1` >> simp[dse_local_agrees_inst_idx] >>
  irule dse_register_pending_step >> metis_tac[]
QED

Theorem dse_register_retained:
  dse_register_opcode inst.inst_opcode ==>
  dse_inst ids sp inst = inst
Proof
  simp[dse_register_opcode_def] >> strip_tac >> Cases_on `sp` >>
  simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def,
       empty_effects_def]
QED

Theorem dse_register_result_cases:
  dse_register_opcode inst.inst_opcode ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  fs[dse_register_opcode_def] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       AllCaseEqs(), exec_pure2_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED
