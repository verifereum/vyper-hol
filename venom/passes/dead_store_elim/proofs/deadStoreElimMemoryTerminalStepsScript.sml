Theory deadStoreElimMemoryTerminalSteps
Ancestors
  deadStoreElimMemoryObserve deadStoreElimTerminalSteps deadStoreElimTerminalEquiv
  deadStoreElimLocal deadStoreElimPending deadStoreElimSafety deadStoreElimDefs
  basePtrDefs memLocDefs venomExecSemantics venomState venomMemDefs venomEffects venomInst list

Theorem dse_memory_terminal_retained:
  inst.inst_opcode IN {RETURN; REVERT} /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} ==>
  dse_inst ids sp inst = inst
Proof
  simp[] >> strip_tac >>
  simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def,
       empty_effects_def, effects_in_space_def]
QED

Theorem dse_memory_terminal_input_bytes:
  inst.inst_opcode IN {RETURN; REVERT} /\
  inst.inst_operands = [offsetop; sizeop] /\
  eval_operand offsetop s = SOME off /\ eval_operand sizeop s = SOME sz /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  allocas_non_overlapping s /\ dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst ==>
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t
Proof
  strip_tac >> Cases_on `sp = AddrSp_Memory`
  >- (gvs[] >> irule dse_precise_input_bytes >>
      rpt (goal_assum (drule_at Any)) >>
      fs[mem_read_ops_def] >> metis_tac[]) >>
  fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def, read_memory_def]
QED

Theorem dse_return_halt_step:
  inst.inst_opcode = RETURN /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
  dse_local_agrees sp P s t /\ dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  allocas_non_overlapping s /\ step_inst fuel ctx inst s = Halt s1 ==>
  ?t1. step_inst fuel ctx inst t = Halt t1 /\ dse_equiv sp s1 t1
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `dse_equiv sp s t` by
    metis_tac[dse_local_agrees_def, dse_pending_space_equiv] >>
  qpat_x_assum `sp IN _` kall_tac >>
  qpat_x_assum `step_inst _ _ _ s = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t` by
    (irule dse_memory_terminal_input_bytes >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  fs[read_memory_def] >>
  simp[dse_equiv_halt_state, dse_equiv_set_returndata]
QED

Theorem dse_revert_abort_step:
  inst.inst_opcode = REVERT /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
  dse_local_agrees sp P s t /\ dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  allocas_non_overlapping s /\ step_inst fuel ctx inst s = Abort a s1 ==>
  ?t1. step_inst fuel ctx inst t = Abort a t1 /\ dse_equiv sp s1 t1
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `dse_equiv sp s t` by
    metis_tac[dse_local_agrees_def, dse_pending_space_equiv] >>
  qpat_x_assum `sp IN _` kall_tac >>
  qpat_x_assum `step_inst _ _ _ s = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t` by
    (irule dse_memory_terminal_input_bytes >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  fs[read_memory_def] >>
  simp[dse_equiv_revert_state, dse_equiv_set_returndata]
QED

Theorem dse_return_result_cases:
  inst.inst_opcode = RETURN ==>
  (?s1. step_inst fuel ctx inst s = Halt s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  CASE_TAC >> simp[] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED

Theorem dse_revert_result_cases:
  inst.inst_opcode = REVERT ==>
  (?s1. step_inst fuel ctx inst s = Abort Revert_abort s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  CASE_TAC >> simp[] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED
