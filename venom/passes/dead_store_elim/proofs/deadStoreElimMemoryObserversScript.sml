Theory deadStoreElimMemoryObservers
Ancestors
  deadStoreElimMemoryObserve deadStoreElimTerminalSteps
  deadStoreElimLocal deadStoreElimPending deadStoreElimLiveness deadStoreElimMemory
  deadStoreElimSafety deadStoreElimDefs deadStoreElimFrame basePtrDefs memLocDefs
  venomExecSemantics venomState venomEffects venomInst list

Theorem dse_local_agrees_logs:
  dse_local_agrees sp P s t ==>
  dse_local_agrees sp P (s with vs_logs := logs) (t with vs_logs := logs)
Proof
  strip_tac >>
  gvs[dse_local_agrees_def, dse_pending_space_def,
       dse_safety_agrees_def, dse_operational_agrees_def,
       dse_equiv_def, dse_pending_memory_def, dse_memory_byte_def,
       lookup_var_def, dse_frame_def, venom_state_component_equality]
QED

Theorem dse_observer_retained:
  inst.inst_opcode IN {SHA3; LOG} /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} ==>
  dse_inst ids sp inst = inst
Proof
  simp[] >> strip_tac >>
  simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def,
       empty_effects_def, effects_in_space_def]
QED

Theorem dse_observer_write_location:
  inst.inst_opcode IN {SHA3; LOG} ==>
  bp_get_write_location bp inst sp = ml_empty
Proof
  simp[] >> strip_tac >> Cases_on `sp` >>
  simp[bp_get_write_location_def, is_raw_fmp_opcode_def,
       write_effects_def, empty_effects_def, effects_in_space_def]
QED

Theorem dse_observer_no_clobber:
  inst.inst_opcode IN {SHA3; LOG} /\ loc.ml_size = SOME n /\ 0 < n ==>
  ~dse_inst_clobbers bp sp loc inst
Proof
  strip_tac >> drule dse_observer_write_location >>
  disch_then (qspec_then `sp` assume_tac) >>
  simp[dse_inst_clobbers_def, ml_empty_def, completely_contains_def]
QED

Theorem dse_observer_pending_step:
  inst.inst_opcode IN {SHA3; LOG} /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\ s1.vs_allocas = s.vs_allocas ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P s1
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[] >>
  irule dse_pending_at_step >> simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  irule dse_observer_no_clobber >> metis_tac[]
QED

Theorem dse_sha3_step:
  inst.inst_opcode = SHA3 /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
  dse_local_agrees sp P s t /\ dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  allocas_non_overlapping s /\ step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P s1 t1 /\
    dse_pending_at cfg bp sp fn bb (SUC idx) P s1 /\
    s1.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  qpat_x_assum `sp IN _` kall_tac >>
  qpat_x_assum `step_inst _ _ _ s = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `read_memory (w2n offset) (w2n size_val) s =
   read_memory (w2n offset) (w2n size_val) t` by
    (Cases_on `sp = AddrSp_Memory`
     >- (gvs[] >> irule dse_sha3_input_bytes >>
         rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
     fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def,
        read_memory_def]) >>
  fs[read_memory_def] >> conj_tac
  >- (irule dse_local_agrees_update_var >> simp[]) >>
  irule dse_observer_pending_step >>
  rpt (goal_assum (drule_at Any)) >> simp[update_var_def] >>
  qexists_tac `s` >> simp[]
QED

Theorem dse_log_step:
  inst.inst_opcode = LOG /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
  dse_local_agrees sp P s t /\ dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  allocas_non_overlapping s /\ step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P s1 t1 /\
    dse_pending_at cfg bp sp fn bb (SUC idx) P s1 /\
    s1.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `!ops. eval_operands ops s = eval_operands ops t` by
    metis_tac[dse_local_agrees_eval_operands] >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_logs = t.vs_logs` by
    fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def,
       dse_frame_def, venom_state_component_equality] >>
  qpat_x_assum `sp IN _` kall_tac >>
  qpat_x_assum `step_inst _ _ _ s = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  IF_CASES_TAC >- simp[] >> pop_assum kall_tac >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t` by
    (Cases_on `sp = AddrSp_Memory`
     >- (gvs[] >> irule dse_log_input_bytes >>
         rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
     fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def,
        read_memory_def]) >>
  fs[read_memory_def] >> conj_tac
  >- (irule dse_local_agrees_logs >> simp[]) >>
  irule dse_observer_pending_step >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexists_tac `s` >> simp[]
QED

Theorem dse_observer_step:
  inst.inst_opcode IN {SHA3; LOG} /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
  dse_local_agrees sp P s t /\ dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  allocas_non_overlapping s /\ step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P s1 t1 /\
    dse_pending_at cfg bp sp fn bb (SUC idx) P s1 /\
    s1.vs_allocas = s.vs_allocas
Proof
  strip_tac >> Cases_on `inst.inst_opcode = SHA3`
  >- (irule dse_sha3_step >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  irule dse_log_step >> rpt (goal_assum (drule_at Any)) >> fs[]
QED

Theorem dse_observer_result_cases:
  inst.inst_opcode IN {SHA3; LOG} /\ ~s.vs_call_ctx.cc_static ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  simp[] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[]
QED
