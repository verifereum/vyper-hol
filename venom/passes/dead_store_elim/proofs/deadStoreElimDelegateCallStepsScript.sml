Theory deadStoreElimDelegateCallSteps
Ancestors
  deadStoreElimCallSteps deadStoreElimExternalUpdates deadStoreElimExternalObservations
  deadStoreElimLocal deadStoreElimPending deadStoreElimSafety deadStoreElimDefs
  deadStoreElimFrame deadStoreElimFrameReadSteps deadStoreElimMemoryObserve
  venomExecSemantics venomState venomEffects venomInst basePtrDefs memLocDefs list
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem dse_extract_venom_result:
  dse_local_agrees AddrSp_Memory P s t /\
  extract_venom_result s out ro rs rr = SOME (v,s1) ==>
  ?t1. extract_venom_result t out ro rs rr = SOME (v,t1) /\
    dse_local_agrees AddrSp_Memory
      (FILTER (\(loc,(b,n)). ~(ro <= b /\ b+n <= ro+LENGTH (TAKE rs s1.vs_returndata))) P)
      s1 t1 /\
    s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas
Proof
  strip_tac >> drule dse_local_agrees_memory_accounts >> strip_tac >>
  drule dse_local_agrees_memory_transient >> strip_tac >>
  `s.vs_outcomes = t.vs_outcomes /\ s.vs_requests = t.vs_requests /\
   s.vs_logs = t.vs_logs /\ s.vs_pending_deletions = t.vs_pending_deletions` by
    fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def,
       dse_frame_def, venom_state_component_equality] >>
  Cases_on `rr` >- gvs[extract_venom_result_def] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  qpat_x_assum `extract_venom_result _ _ _ _ _ = _` mp_tac >>
  simp[extract_venom_result_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  namedCases_on `pair0` ["err", "opt"]
  >- suspend "error" >>
  Cases_on `opt` >- suspend "success" >> suspend "revert"
QED

Resume dse_extract_venom_result[error]:
  FULL_SIMP_TAC bool_ss [sumTheory.sum_case_def, optionTheory.option_case_def,
    pairTheory.PAIR_EQ, optionTheory.SOME_11, pairTheory.UNCURRY_DEF] >>
  qpat_x_assum `_ = s1` (SUBST_ALL_TAC o SYM) >>
  simp_tac bool_ss [write_memory_with_expansion_def, LET_THM,
    venom_state_accfupds, venom_state_fupdcanon, combinTheory.K_THM] >>
  irule (SIMP_RULE bool_ss [write_memory_with_expansion_def, LET_THM,
    venom_state_accfupds, venom_state_fupdcanon, combinTheory.K_THM, DE_MORGAN_THM]
    dse_external_memory_update_keep_queues) >> first_assum ACCEPT_TAC
QED

Resume dse_extract_venom_result[success]:
  FULL_SIMP_TAC bool_ss [sumTheory.sum_case_def, optionTheory.option_case_def,
    pairTheory.PAIR_EQ, optionTheory.SOME_11, pairTheory.UNCURRY_DEF] >>
  qpat_x_assum `_ = s1` (SUBST_ALL_TAC o SYM) >>
  simp_tac bool_ss [write_memory_with_expansion_def, LET_THM,
    venom_state_accfupds, venom_state_fupdcanon, combinTheory.K_THM] >>
  irule (SIMP_RULE bool_ss [write_memory_with_expansion_def, LET_THM,
    venom_state_accfupds, venom_state_fupdcanon, combinTheory.K_THM, DE_MORGAN_THM]
    dse_external_memory_update_keep_queues) >> first_assum ACCEPT_TAC
QED

Resume dse_extract_venom_result[revert]:
  FULL_SIMP_TAC bool_ss [sumTheory.sum_case_def, optionTheory.option_case_def,
    pairTheory.PAIR_EQ, optionTheory.SOME_11, pairTheory.UNCURRY_DEF] >>
  qpat_x_assum `_ = s1` (SUBST_ALL_TAC o SYM) >>
  simp_tac bool_ss [write_memory_with_expansion_def, LET_THM,
    venom_state_accfupds, venom_state_fupdcanon, combinTheory.K_THM] >>
  irule (SIMP_RULE bool_ss [write_memory_with_expansion_def, LET_THM,
    venom_state_accfupds, venom_state_fupdcanon, combinTheory.K_THM, DE_MORGAN_THM]
    dse_external_memory_update_keep_queues) >> first_assum ACCEPT_TAC
QED

Finalise dse_extract_venom_result

Theorem dse_exec_delegatecall_ok:
  dse_local_agrees AddrSp_Memory P s t /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t /\
  exec_delegatecall inst s gas addr off sz ro rs = OK s1 ==>
  ?t1. exec_delegatecall inst t gas addr off sz ro rs = OK t1 /\
    dse_local_agrees AddrSp_Memory
      (FILTER (\(loc,(b,n)). ~(w2n ro <= b /\ b+n <= w2n ro+LENGTH (TAKE (w2n rs) s1.vs_returndata))) P)
      s1 t1 /\
    s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas
Proof
  strip_tac >>
  drule dse_local_agrees_memory_accounts >> strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (drule dse_local_agrees_frame >> simp[]) >>
  drule dse_local_agrees_delegatecall_state >> strip_tac >>
  qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[exec_delegatecall_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all dse_extract_venom_result >> strip_tac >>
  simp[] >>
  irule dse_local_agrees_update_var >>
  qpat_x_assum `dse_local_agrees _ (FILTER _ _) _ _` mp_tac >>
  simp_tac bool_ss [arithmeticTheory.ADD_COMM, DE_MORGAN_THM]
QED

Theorem dse_delegatecall_memory_step:
  inst.inst_opcode = DELEGATECALL /\
  dse_local_agrees AddrSp_Memory P s t /\
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  allocas_non_overlapping s /\ step_inst fuel ctx inst s = OK s1 ==>
  ?t1 P1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees AddrSp_Memory P1 s1 t1 /\
    dse_pending_at cfg bp AddrSp_Memory fn bb (SUC idx) P1 s1 /\
    s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  qpat_x_assum `step_inst _ _ _ s = _` mp_tac >>
  fs[] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `read_memory (w2n ao) (w2n as_) s = read_memory (w2n ao) (w2n as_) t` by
    (irule dse_precise_input_bytes >>
     rpt (goal_assum (drule_at Any)) >> simp[mem_read_ops_def] >> metis_tac[]) >>
  drule_all dse_exec_delegatecall_ok >> strip_tac >>
  qexistsl_tac [`t1`, `FILTER (\(loc,(b,n)).
    ~(w2n ro <= b /\ b+n <= w2n ro+LENGTH (TAKE (w2n rs) s1.vs_returndata))) P`] >>
  fs[] >>
  irule dse_pending_at_filter >> irule dse_external_pending_step >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

Theorem dse_exec_delegatecall_results:
  (?s1. exec_delegatecall inst s gas addr ao sz ro rs = OK s1) \/
  (?e. exec_delegatecall inst s gas addr ao sz ro rs = Error e)
Proof
  simp[exec_delegatecall_def] >>
  Cases_on `extract_venom_result s 1w (w2n ro) (w2n rs)
    (run (make_venom_delegatecall_state s (w2w addr) (w2n gas)
      (read_memory (w2n ao) (w2n sz) s)
      (lookup_account (w2w addr) s.vs_accounts).code s.vs_call_ctx.cc_static))` >> simp[] >>
  rename1 `SOME result` >> PairCases_on `result` >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `h::rest` >> Cases_on `rest` >> simp[]
QED

Theorem dse_delegatecall_results:
  inst.inst_opcode = DELEGATECALL ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  fs[] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rpt strip_tac >>
  metis_tac[dse_exec_delegatecall_results, exec_result_distinct]
QED
