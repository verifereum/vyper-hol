Theory deadStoreElimAllocationSteps
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimLiveness
  deadStoreElimMemory deadStoreElimSafety deadStoreElimDefs
  venomExecSemantics venomState venomEffects venomInst basePtrDefs memLocDefs finite_map
  deadStoreElimFrame
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem dse_local_agrees_allocation_fields:
  dse_local_agrees sp P s t ==>
  dse_local_agrees sp P
    (s with <|vs_allocas := allocas; vs_alloca_next := next|>)
    (t with <|vs_allocas := allocas; vs_alloca_next := next|>)
Proof
  strip_tac >>
  gvs[dse_local_agrees_def, dse_pending_space_def,
      dse_safety_agrees_def, dse_operational_agrees_def,
      dse_equiv_def, dse_pending_memory_def, dse_memory_byte_def,
      lookup_var_def]
QED

Theorem dse_exec_alloca_local:
  dse_local_agrees sp P s t /\ exec_alloca inst s sz = OK s1 ==>
  ?t1. exec_alloca inst t sz = OK t1 /\ dse_local_agrees sp P s1 t1
Proof
  strip_tac >>
  `s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next` by
    fs[dse_local_agrees_def, dse_safety_agrees_def] >>
  gvs[exec_alloca_def, AllCaseEqs()] >>
  simp[dse_local_agrees_update_var, dse_local_agrees_allocation_fields]
QED

Theorem dse_exec_alloca_old_lookup:
  exec_alloca inst s sz = OK s1 /\ FLOOKUP s.vs_allocas aid = SOME pair ==>
  FLOOKUP s1.vs_allocas aid = SOME pair
Proof
  strip_tac >> gvs[exec_alloca_def, AllCaseEqs(), update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[]
QED

Theorem dse_alloca_local_step:
  inst.inst_opcode = ALLOCA /\ dse_local_agrees sp P s t /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\ dse_local_agrees sp P s1 t1
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  drule_all dse_exec_alloca_local >> metis_tac[]
QED

Theorem dse_alloca_old_lookup:
  inst.inst_opcode = ALLOCA /\ step_inst fuel ctx inst s = OK s1 /\
  FLOOKUP s.vs_allocas aid = SOME pair ==>
  FLOOKUP s1.vs_allocas aid = SOME pair
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  drule_all dse_exec_alloca_old_lookup >> simp[]
QED

Theorem dse_alloca_write_location:
  inst.inst_opcode = ALLOCA ==> bp_get_write_location bp inst sp = ml_empty
Proof
  strip_tac >> Cases_on `sp` >>
  simp[bp_get_write_location_def, is_raw_fmp_opcode_def,
       write_effects_def, empty_effects_def]
QED

Theorem dse_alloca_no_clobber:
  inst.inst_opcode = ALLOCA /\ loc.ml_size = SOME n /\ 0 < n ==>
  ~dse_inst_clobbers bp sp loc inst
Proof
  strip_tac >> drule dse_alloca_write_location >>
  disch_then (qspec_then `sp` assume_tac) >>
  simp[dse_inst_clobbers_def, ml_empty_def, completely_contains_def]
QED

Theorem dse_alloca_pending_step:
  inst.inst_opcode = ALLOCA /\ step_inst fuel ctx inst s = OK s1 /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P s1
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> conj_tac
  >- (rpt strip_tac >> drule_all dse_alloca_old_lookup >> simp[]) >>
  irule dse_pending_at_step >> simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  irule dse_alloca_no_clobber >> metis_tac[]
QED

Theorem dse_local_agrees_alloca_step:
  inst.inst_opcode = ALLOCA /\ dse_local_agrees sp P s t /\
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
  drule_all dse_alloca_local_step >> strip_tac >>
  qexists_tac `t1` >> simp[dse_local_agrees_inst_idx] >>
  irule dse_alloca_pending_step >> metis_tac[]
QED

Theorem dse_alloca_retained:
  inst.inst_opcode = ALLOCA ==> dse_inst ids sp inst = inst
Proof
  strip_tac >> Cases_on `sp` >>
  simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def,
       empty_effects_def]
QED

Theorem dse_alloca_result_cases:
  inst.inst_opcode = ALLOCA ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       AllCaseEqs(), exec_alloca_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED
