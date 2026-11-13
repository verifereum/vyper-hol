Theory deadStoreElimAssertionSteps
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimLiveness
  deadStoreElimMemory deadStoreElimSafety deadStoreElimDefs
  deadStoreElimTerminalEquiv basePtrDefs memLocDefs
  venomExecSemantics venomState venomEffects venomInst list
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem dse_assertion_retained:
  inst.inst_opcode IN {ASSERT; ASSERT_UNREACHABLE; INVALID; PHI} /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} ==>
  dse_inst ids sp inst = inst
Proof
  simp[] >> strip_tac >>
  simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def,
       empty_effects_def, effects_in_space_def]
QED

Theorem dse_assertion_write_location:
  inst.inst_opcode IN {ASSERT; ASSERT_UNREACHABLE; INVALID; PHI} ==>
  bp_get_write_location bp inst sp = ml_empty
Proof
  simp[] >> strip_tac >> Cases_on `sp` >>
  simp[bp_get_write_location_def, is_raw_fmp_opcode_def,
       write_effects_def, empty_effects_def]
QED

Theorem dse_assertion_no_clobber:
  inst.inst_opcode IN {ASSERT; ASSERT_UNREACHABLE; INVALID; PHI} /\
  loc.ml_size = SOME n /\ 0 < n ==>
  ~dse_inst_clobbers bp sp loc inst
Proof
  strip_tac >> drule dse_assertion_write_location >>
  disch_then (qspec_then `sp` assume_tac) >>
  simp[dse_inst_clobbers_def, ml_empty_def, completely_contains_def]
QED

Theorem dse_assertion_local_step:
  inst.inst_opcode IN {ASSERT; ASSERT_UNREACHABLE; INVALID; PHI} /\
  dse_local_agrees sp P s t /\ step_inst fuel ctx inst s = OK s1 ==>
  step_inst fuel ctx inst t = OK t /\ s1 = s
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >>
     metis_tac[dse_safety_agrees_eval_operand]) >>
  fs[] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Theorem dse_assertion_pending_step:
  inst.inst_opcode IN {ASSERT; ASSERT_UNREACHABLE; INVALID; PHI} /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P s
Proof
  strip_tac >> irule dse_pending_at_step >> simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  irule dse_assertion_no_clobber >> metis_tac[]
QED

Theorem dse_local_agrees_assertion_step:
  inst.inst_opcode IN {ASSERT; ASSERT_UNREACHABLE; INVALID; PHI} /\
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
  drule_all dse_assertion_local_step >> strip_tac >> gvs[] >>
  simp[dse_local_agrees_inst_idx] >>
  irule dse_assertion_pending_step >> simp[]
QED

Theorem dse_assertion_abort_step:
  inst.inst_opcode IN {ASSERT; ASSERT_UNREACHABLE; INVALID; PHI} /\
  dse_local_agrees sp P s t /\ step_inst fuel ctx inst s = Abort a s1 ==>
  ?t1. step_inst fuel ctx inst t = Abort a t1 /\ dse_equiv sp s1 t1
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >>
     metis_tac[dse_safety_agrees_eval_operand]) >>
  `dse_equiv sp s t` by
    metis_tac[dse_local_agrees_def, dse_pending_space_equiv] >>
  fs[] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[dse_equiv_halt_state, dse_equiv_revert_state, dse_equiv_set_returndata]
QED

Theorem dse_phi_error:
  inst.inst_opcode = PHI ==> step_inst fuel ctx inst s = Error "phi outside prefix"
Proof
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED

Theorem dse_invalid_abort:
  inst.inst_opcode = INVALID ==>
  step_inst fuel ctx inst s = Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED

Theorem dse_assertion_result_cases:
  inst.inst_opcode IN {ASSERT; ASSERT_UNREACHABLE; INVALID; PHI} ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?a s1. step_inst fuel ctx inst s = Abort a s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  simp[] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  namedCases_on `inst.inst_operands` ["", "op ops"] >> simp[] >>
  Cases_on `ops` >> simp[] >>
  Cases_on `eval_operand op s` >> simp[] >>
  IF_CASES_TAC >> simp[]
QED
