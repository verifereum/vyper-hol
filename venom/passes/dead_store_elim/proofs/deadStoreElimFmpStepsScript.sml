Theory deadStoreElimFmpSteps
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimLiveness
  deadStoreElimMemory deadStoreElimSafety deadStoreElimDefs basePtrDefs memLocDefs
  venomExecSemantics venomState venomEffects venomInst list
  deadStoreElimFrame

Theorem dse_local_agrees_fmp:
  dse_local_agrees sp P s t ==>
  dse_local_agrees sp P (s with vs_fmp := v) (t with vs_fmp := v)
Proof
  strip_tac >>
  gvs[dse_local_agrees_def, dse_pending_space_def,
      dse_safety_agrees_def, dse_operational_agrees_def,
      dse_equiv_def, dse_pending_memory_def, dse_memory_byte_def,
      lookup_var_def]
QED

Theorem dse_fmp_retained:
  inst.inst_opcode IN {GETFMP; SETFMP; DALLOCA} /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} ==>
  dse_inst ids sp inst = inst
Proof
  simp[] >> strip_tac >>
  simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def,
       empty_effects_def, effects_in_space_def]
QED

Theorem dse_fmp_write_location:
  inst.inst_opcode IN {GETFMP; SETFMP; DALLOCA} ==>
  bp_get_write_location bp inst sp = ml_empty
Proof
  simp[] >> strip_tac >>
  Cases_on `sp` >>
  simp[bp_get_write_location_def, is_raw_fmp_opcode_def,
       write_effects_def, empty_effects_def]
QED

Theorem dse_fmp_no_clobber:
  inst.inst_opcode IN {GETFMP; SETFMP; DALLOCA} /\
  loc.ml_size = SOME n /\ 0 < n ==>
  ~dse_inst_clobbers bp sp loc inst
Proof
  strip_tac >> drule dse_fmp_write_location >>
  disch_then (qspec_then `sp` assume_tac) >>
  simp[dse_inst_clobbers_def, ml_empty_def, completely_contains_def]
QED

Theorem dse_fmp_local_step:
  inst.inst_opcode IN {GETFMP; SETFMP; DALLOCA} /\
  dse_local_agrees sp P s t /\ step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
       dse_local_agrees sp P s1 t1 /\ s1.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >>
     metis_tac[dse_safety_agrees_eval_operand]) >>
  `s.vs_fmp = t.vs_fmp` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  fs[] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[dse_local_agrees_update_var, dse_local_agrees_fmp, update_var_def]
QED

Theorem dse_fmp_pending_step:
  inst.inst_opcode IN {GETFMP; SETFMP; DALLOCA} /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\ s1.vs_allocas = s.vs_allocas ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P s1
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[] >>
  irule dse_pending_at_step >> simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  irule dse_fmp_no_clobber >> metis_tac[]
QED

Theorem dse_local_agrees_fmp_step:
  inst.inst_opcode IN {GETFMP; SETFMP; DALLOCA} /\
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
  drule_all dse_fmp_local_step >> strip_tac >>
  qexists_tac `t1` >> simp[dse_local_agrees_inst_idx] >>
  irule dse_fmp_pending_step >> metis_tac[]
QED

Theorem dse_fmp_result_cases:
  inst.inst_opcode IN {GETFMP; SETFMP; DALLOCA} ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  simp[] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
  >- (namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[] >>
      Cases_on `outs` >> simp[] >>
      Cases_on `inst.inst_operands` >> simp[])
  >- (namedCases_on `inst.inst_operands` ["", "op ops"] >> simp[] >>
      Cases_on `ops` >> simp[] >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      Cases_on `eval_operand op s` >> simp[]) >>
  namedCases_on `inst.inst_operands` ["", "op ops"]
  >- simp[] >>
  Cases_on `ops` >> simp[] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[] >>
  Cases_on `outs` >> simp[] >>
  Cases_on `eval_operand op s` >> simp[]
QED
