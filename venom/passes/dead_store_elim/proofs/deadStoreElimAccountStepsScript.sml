Theory deadStoreElimAccountSteps
Ancestors
  deadStoreElimExternalObservations deadStoreElimFrameReadSteps
  deadStoreElimLocal deadStoreElimPending deadStoreElimLiveness
  deadStoreElimSafety deadStoreElimDefs basePtrDefs memLocDefs
  venomExecSemantics venomState venomEffects venomInst list

Definition dse_account_opcode_def:
  dse_account_opcode opc <=>
    opc IN {BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH}
End

Theorem dse_account_common_update:
  dse_account_opcode inst.inst_opcode /\ dse_local_agrees sp P s t /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?out w. s1 = update_var out w s /\
    step_inst fuel ctx inst t = OK (update_var out w t)
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `!addr. (lookup_account addr s.vs_accounts).balance =
          (lookup_account addr t.vs_accounts).balance` by
    metis_tac[dse_local_agrees_account_balance] >>
  `!addr. (lookup_account addr s.vs_accounts).code =
          (lookup_account addr t.vs_accounts).code` by
    metis_tac[dse_local_agrees_account_code] >>
  `!addr. account_empty (lookup_account addr s.vs_accounts) =
          account_empty (lookup_account addr t.vs_accounts)` by
    metis_tac[dse_local_agrees_account_empty] >>
  drule dse_local_agrees_frame >> strip_tac >>
  fs[dse_account_opcode_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  FIRST [irule exec_read0_common_update, irule exec_read1_common_update] >>
  simp[] >> metis_tac[]
QED

Theorem dse_account_result_cases:
  dse_account_opcode inst.inst_opcode ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  simp[dse_account_opcode_def] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_read0_result_cases, exec_read1_result_cases]
QED

Theorem dse_account_retained:
  dse_account_opcode inst.inst_opcode /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} ==>
  dse_inst ids sp inst = inst
Proof
  simp[dse_account_opcode_def] >> strip_tac >>
  simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def,
       empty_effects_def]
QED

Theorem dse_account_write_location:
  dse_account_opcode inst.inst_opcode ==>
  bp_get_write_location bp inst sp = ml_empty
Proof
  simp[dse_account_opcode_def] >> strip_tac >> Cases_on `sp` >>
  simp[bp_get_write_location_def, is_raw_fmp_opcode_def,
       write_effects_def, empty_effects_def]
QED

Theorem dse_account_no_clobber:
  dse_account_opcode inst.inst_opcode /\ loc.ml_size = SOME n /\ 0 < n ==>
  ~dse_inst_clobbers bp sp loc inst
Proof
  strip_tac >> drule dse_account_write_location >>
  disch_then (qspec_then `sp` assume_tac) >>
  simp[dse_inst_clobbers_def, ml_empty_def, completely_contains_def]
QED

Theorem dse_account_pending_step:
  dse_account_opcode inst.inst_opcode /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P (update_var out w s)
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[update_var_def] >>
  irule dse_pending_at_step >> simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  irule dse_account_no_clobber >> metis_tac[]
QED

Theorem dse_local_agrees_account_step:
  dse_account_opcode inst.inst_opcode /\ dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp sp fn bb (SUC s.vs_inst_idx) P s1
Proof
  strip_tac >> drule_all dse_account_common_update >> strip_tac >>
  qexists_tac `update_var out w t` >> simp[] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  conj_tac
  >- (gvs[] >> irule dse_local_agrees_inst_idx >>
      irule dse_local_agrees_update_var >> simp[]) >>
  gvs[] >> irule dse_account_pending_step >>
  fs[get_instruction_def, AllCaseEqs()]
QED
