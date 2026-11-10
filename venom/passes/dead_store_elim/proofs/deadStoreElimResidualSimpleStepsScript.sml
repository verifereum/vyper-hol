Theory deadStoreElimResidualSimpleSteps
Ancestors
  deadStoreElimBarrierSteps deadStoreElimExternalObservations deadStoreElimTerminalEquiv
  deadStoreElimLocal deadStoreElimPending deadStoreElimSafety deadStoreElimDefs
  deadStoreElimFrame deadStoreElimFrameReadSteps
  venomExecSemantics venomState venomEffects venomInst basePtrDefs memLocDefs list
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem dse_key_memory_reader_common_update:
  inst.inst_opcode IN {MEMTOP; ILOAD} /\
  sp IN {AddrSp_Storage; AddrSp_Transient} /\
  dse_local_agrees sp P s t /\ step_inst fuel ctx inst s = OK s1 ==>
  ?out w. s1 = update_var out w s /\
    step_inst fuel ctx inst t = OK (update_var out w t)
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `s.vs_memory = t.vs_memory` by
    fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def] >>
  fs[] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  FIRST [irule exec_read0_common_update, irule exec_read1_common_update] >>
  simp[mload_def] >> metis_tac[]
QED

Theorem dse_key_memory_reader_step:
  inst.inst_opcode IN {MEMTOP; ILOAD} /\
  sp IN {AddrSp_Storage; AddrSp_Transient} /\
  dse_local_agrees sp P s t /\ step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P s1 t1 /\
    s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas
Proof
  strip_tac >> drule_all dse_key_memory_reader_common_update >> strip_tac >>
  qexists_tac `update_var out w t` >> gvs[] >>
  simp[] >> irule dse_local_agrees_update_var >> simp[]
QED

Theorem dse_key_memory_reader_write_location:
  inst.inst_opcode IN {MEMTOP; ILOAD} /\
  sp IN {AddrSp_Storage; AddrSp_Transient} ==>
  bp_get_write_location bp inst sp = ml_empty
Proof
  simp[] >> strip_tac >>
  simp[bp_get_write_location_def, is_raw_fmp_opcode_def,
       write_effects_def, empty_effects_def]
QED

Theorem dse_key_memory_reader_no_clobber:
  inst.inst_opcode IN {MEMTOP; ILOAD} /\
  sp IN {AddrSp_Storage; AddrSp_Transient} /\ loc.ml_size = SOME n /\ 0 < n ==>
  ~dse_inst_clobbers bp sp loc inst
Proof
  strip_tac >> drule_all dse_key_memory_reader_write_location >> strip_tac >>
  simp[dse_inst_clobbers_def, ml_empty_def, completely_contains_def]
QED

Theorem dse_key_memory_reader_pending_step:
  inst.inst_opcode IN {MEMTOP; ILOAD} /\
  sp IN {AddrSp_Storage; AddrSp_Transient} /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\ s1.vs_allocas = s.vs_allocas ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P s1
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[] >>
  irule dse_pending_at_step >> simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  irule dse_key_memory_reader_no_clobber >> metis_tac[]
QED

Theorem dse_memory_reader_results:
  inst.inst_opcode IN {MEMTOP; ILOAD} ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  simp[] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
    exec_read0_result_cases, exec_read1_result_cases]
QED

Theorem dse_memory_reader_retained:
  inst.inst_opcode IN {MEMTOP; ILOAD} /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} ==>
  dse_inst ids sp inst = inst
Proof
  simp[] >> strip_tac >>
  simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def, empty_effects_def]
QED

Theorem dse_equiv_memory_accounts:
  dse_equiv AddrSp_Memory s t ==>
  dse_equiv AddrSp_Memory (s with vs_accounts := ac) (t with vs_accounts := ac)
Proof
  simp[dse_equiv_def, lookup_var_def]
QED

Theorem dse_equiv_pending_deletions[local]:
  dse_equiv sp s t ==>
  dse_equiv sp (s with vs_pending_deletions := d) (t with vs_pending_deletions := d)
Proof
  rw[dse_equiv_def, lookup_var_def] >>
  fs[dse_frame_def, venom_state_component_equality]
QED

Theorem dse_selfdestruct_memory_step:
  inst.inst_opcode = SELFDESTRUCT /\
  dse_local_agrees AddrSp_Memory P s t /\ step_inst fuel ctx inst s = Halt s1 ==>
  ?t1. step_inst fuel ctx inst t = Halt t1 /\ dse_equiv AddrSp_Memory s1 t1
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `!ops. eval_operands ops s = eval_operands ops t` by
    (Induct >> simp[eval_operands_def] >> gen_tac >> CASE_TAC >> simp[]) >>
  drule dse_local_agrees_memory_accounts >> strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (drule dse_local_agrees_frame >> simp[]) >>
  qpat_x_assum `step_inst _ _ _ s = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  irule dse_equiv_halt_state >> irule dse_equiv_set_returndata >>
  irule dse_equiv_memory_accounts >>
  `s.vs_pending_deletions = t.vs_pending_deletions` by
    fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def,
       dse_frame_def, venom_state_component_equality] >>
  pop_assum SUBST1_TAC >> irule dse_equiv_pending_deletions >>
  irule dse_pending_space_equiv >> qexists_tac `P` >> fs[dse_local_agrees_def]
QED

Theorem dse_selfdestruct_results:
  inst.inst_opcode = SELFDESTRUCT /\ ~s.vs_call_ctx.cc_static ==>
  (?s1. step_inst fuel ctx inst s = Halt s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `h::rest` >> Cases_on `rest` >> simp[] >>
  Cases_on `eval_operand h s` >> simp[]
QED

Theorem dse_selfdestruct_retained:
  inst.inst_opcode = SELFDESTRUCT /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
  wf_function fn /\ all_dead_stores ids cfg aliases bp sp fn /\ MEM inst (fn_insts fn) ==>
  dse_inst ids sp inst = inst
Proof
  strip_tac >> Cases_on `sp = AddrSp_Memory`
  >- simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def, empty_effects_def] >>
  irule dse_barrier_retained >>
  simp[dse_barrier_case_def] >>
  conj_tac >- fs[] >>
  rpt (goal_assum (drule_at Any))
QED
