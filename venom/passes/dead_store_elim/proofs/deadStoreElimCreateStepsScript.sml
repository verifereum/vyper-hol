Theory deadStoreElimCreateSteps
Ancestors
  deadStoreElimMemoryObserve deadStoreElimExternalObservations
  deadStoreElimExternalUpdates deadStoreElimFrameReadSteps
  deadStoreElimLocal deadStoreElimPending deadStoreElimDefs deadStoreElimFrame
  deadStoreElimSafety deadStoreElimTerminalEquiv basePtrDefs memLocDefs
  venomCallOracleDefs venomExecSemantics venomState venomEffects venomInst list

Theorem dse_create_request:
  dse_local_agrees AddrSp_Memory P s t /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t ==>
  venom_create_request s value off sz salt = venom_create_request t value off sz salt
Proof
  strip_tac >> drule dse_local_agrees_memory_accounts >> strip_tac >>
  drule dse_local_agrees_memory_transient >> strip_tac >>
  simp[venom_create_request_def]
QED

Theorem dse_consume_create_outcome:
  dse_local_agrees AddrSp_Memory P s t /\
  consume_create_outcome rq s = (v,s1) ==>
  ?t1. consume_create_outcome rq t = (v,t1) /\
    dse_local_agrees AddrSp_Memory P s1 t1 /\
    s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas
Proof
  strip_tac >> drule dse_local_agrees_memory_accounts >> strip_tac >>
  drule dse_local_agrees_memory_transient >> strip_tac >>
  drule dse_local_agrees_frame >> strip_tac >>
  `s.vs_outcomes = t.vs_outcomes /\ s.vs_requests = t.vs_requests /\
   s.vs_logs = t.vs_logs /\ s.vs_pending_deletions = t.vs_pending_deletions` by
    fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def,
       dse_frame_def, venom_state_component_equality] >>
  gvs[consume_create_outcome_eq] >>
  irule (SRULE [dse_external_update_def] dse_local_agrees_external_update) >> simp[]
QED

Theorem dse_exec_create_ok:
  dse_local_agrees AddrSp_Memory P s t /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t /\
  exec_create inst s value off sz salt = OK s1 ==>
  ?t1. exec_create inst t value off sz salt = OK t1 /\
    dse_local_agrees AddrSp_Memory P s1 t1 /\ s1.vs_allocas = s.vs_allocas
Proof
  strip_tac >> drule_all dse_create_request >> strip_tac >>
  qpat_x_assum `exec_create _ _ _ _ _ _ = _` mp_tac >>
  simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
  strip_tac >> gvs[AllCaseEqs(), Excl "consume_create_outcome_eq"] >>
  namedCases_on `consume_create_outcome (venom_create_request t value off sz salt) s`
    ["output source"] >> gvs[Excl "consume_create_outcome_eq"] >>
  drule_all dse_consume_create_outcome >> strip_tac >>
  simp[Excl "consume_create_outcome_eq"] >>
  irule dse_local_agrees_update_var >> simp[]
QED

Theorem dse_create_not_effects_in_space:
  inst.inst_opcode IN {CREATE; CREATE2} ==>
  ~effects_in_space sp inst
Proof
  simp[] >> strip_tac >> Cases_on `sp` >>
  gvs[effects_in_space_def, write_effects_def, read_effects_def,
      all_effects_def, empty_effects_def, pred_setTheory.SUBSET_DEF]
QED

Theorem dse_create_memory_retained:
  inst.inst_opcode IN {CREATE; CREATE2} /\ inst.inst_id NOTIN ids ==>
  dse_inst ids AddrSp_Memory inst = inst
Proof
  simp[dse_inst_def]
QED

Theorem dse_create_memory_step:
  inst.inst_opcode IN {CREATE; CREATE2} /\
  dse_local_agrees AddrSp_Memory P s t /\
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  allocas_non_overlapping s /\ step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees AddrSp_Memory P s1 t1 /\
    dse_pending_at cfg bp AddrSp_Memory fn bb (SUC idx) P s1 /\
    s1.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `!ops. eval_operands ops s = eval_operands ops t` by
    (Induct >> simp[eval_operands_def] >> gen_tac >> CASE_TAC >> simp[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (drule dse_local_agrees_frame >> simp[]) >>
  qpat_x_assum `step_inst _ _ _ s = _` mp_tac >>
  fs[] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
               Excl "consume_create_outcome_eq"] >>
  IF_CASES_TAC >- simp[] >> pop_assum kall_tac >>
  strip_tac >> gvs[AllCaseEqs(), Excl "consume_create_outcome_eq"] >>
  `read_memory (w2n offset) (w2n sz) s =
   read_memory (w2n offset) (w2n sz) t` by
    (irule dse_precise_input_bytes >>
     rpt (goal_assum (drule_at Any)) >> simp[mem_read_ops_def] >> metis_tac[]) >>
  drule_all dse_exec_create_ok >> strip_tac >>
  qexists_tac `t1` >> simp[] >>
  irule dse_external_pending_step >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

(* Arbitrary ids need not satisfy all_dead_stores; not a frozen-theorem counterexample. *)
Theorem dse_create_key_retention_counterexample:
  dse_inst {0} AddrSp_Storage (mk_inst 0 CREATE [] []) <>
    mk_inst 0 CREATE [] []
Proof
  EVAL_TAC
QED

Theorem dse_create_result_cases:
  inst.inst_opcode IN {CREATE; CREATE2} ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e) \/
  (?s1. step_inst fuel ctx inst s = Abort ExHalt_abort s1)
Proof
  strip_tac >> Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  fs[] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
              AllCaseEqs(), exec_create_not_Halt, exec_create_not_IntRet,
              exec_create_abort_iff] >>
  rpt strip_tac >> gvs[]
QED

Theorem dse_create_memory_abort:
  inst.inst_opcode IN {CREATE; CREATE2} /\
  inst.inst_id NOTIN ids /\
  dse_local_agrees AddrSp_Memory P s t /\
  step_inst fuel ctx inst s = Abort reason s1 ==>
  ?t1. step_inst fuel ctx (dse_inst ids AddrSp_Memory inst) t = Abort reason t1 /\
    dse_equiv AddrSp_Memory s1 t1
Proof
  strip_tac >> simp[dse_inst_def] >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `!ops. eval_operands ops s = eval_operands ops t` by
    (Induct >> simp[eval_operands_def] >> gen_tac >> CASE_TAC >> simp[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (drule dse_local_agrees_frame >> simp[]) >>
  `dse_equiv AddrSp_Memory s t` by
    fs[dse_local_agrees_def, dse_pending_space_def] >>
  qpat_x_assum `step_inst _ _ _ s = _` mp_tac >>
  fs[] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  IF_CASES_TAC
  >- (simp[] >> strip_tac >> gvs[] >>
      irule dse_equiv_halt_state >> irule dse_equiv_set_returndata >> simp[]) >>
  pop_assum kall_tac >>
  simp[AllCaseEqs(), exec_create_abort_iff] >>
  strip_tac >> gvs[] >>
  irule dse_equiv_halt_state >> irule dse_equiv_set_returndata >> simp[]
QED
