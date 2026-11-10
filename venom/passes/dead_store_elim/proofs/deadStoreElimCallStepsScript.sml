Theory deadStoreElimCallSteps
Ancestors
  deadStoreElimCreateSteps deadStoreElimExternalUpdates deadStoreElimStoreSteps
  deadStoreElimExternalObservations deadStoreElimLocal deadStoreElimPending
  deadStoreElimDefs deadStoreElimSafety deadStoreElimMemoryObserve
  deadStoreElimFrameReadSteps deadStoreElimFrame basePtrDefs memLocDefs
  venomCallOracleDefs venomExecSemantics venomState venomEffects venomInst list
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem dse_call_request:
  dse_local_agrees AddrSp_Memory P s t /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t ==>
  venom_call_request s addr value off sz is_static =
  venom_call_request t addr value off sz is_static
Proof
  strip_tac >> drule dse_local_agrees_memory_accounts >> strip_tac >>
  drule dse_local_agrees_memory_transient >> strip_tac >>
  drule dse_local_agrees_frame >> strip_tac >>
  simp[venom_call_request_def]
QED

Theorem dse_external_memory_update:
  dse_local_agrees AddrSp_Memory P s t ==>
  dse_local_agrees AddrSp_Memory
    (FILTER (\(loc,(b,n)). ~(a <= b /\ b+n <= a+LENGTH bytes)) P)
    (dse_external_update ac ts logs dels rd os rqs (write_memory_with_expansion a bytes s))
    (dse_external_update ac ts logs dels rd os rqs (write_memory_with_expansion a bytes t))
Proof
  strip_tac >> irule dse_local_agrees_external_update >>
  irule dse_local_agrees_memory_overwrite >> simp[]
QED

Theorem dse_external_record_keep_queues[local]:
  os = s.vs_outcomes /\ rqs = s.vs_requests ==>
  (s with <|vs_accounts := ac; vs_transient := ts; vs_logs := logs;
    vs_pending_deletions := dels; vs_returndata := rd;
    vs_outcomes := os; vs_requests := rqs|>) =
  (s with <|vs_accounts := ac; vs_transient := ts; vs_logs := logs;
    vs_pending_deletions := dels; vs_returndata := rd|>)
Proof
  simp[venom_state_component_equality]
QED

Theorem dse_external_memory_update_keep_queues:
  dse_local_agrees AddrSp_Memory P s t ==>
  dse_local_agrees AddrSp_Memory
    (FILTER (\(loc,(b,n)). ~(a <= b /\ b+n <= a+LENGTH bytes)) P)
    ((write_memory_with_expansion a bytes s) with
      <|vs_accounts := ac; vs_transient := ts; vs_logs := logs;
        vs_pending_deletions := dels; vs_returndata := rd|>)
    ((write_memory_with_expansion a bytes t) with
      <|vs_accounts := ac; vs_transient := ts; vs_logs := logs;
        vs_pending_deletions := dels; vs_returndata := rd|>)
Proof
  strip_tac >>
  `s.vs_outcomes = t.vs_outcomes /\ s.vs_requests = t.vs_requests` by
    fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def,
       dse_frame_def, venom_state_component_equality] >>
  drule dse_external_memory_update >>
  disch_then (qspecl_then [`ts`, `s.vs_requests`, `rd`, `s.vs_outcomes`] mp_tac) >>
  simp[dse_external_update_def, dse_external_record_keep_queues,
       write_memory_with_expansion_def] >>
  disch_then irule
QED

Theorem dse_consume_call_outcome:
  dse_local_agrees AddrSp_Memory P s t /\
  consume_call_outcome rq ro rs s = (v,s1) ==>
  ?t1. consume_call_outcome rq ro rs t = (v,t1) /\
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
  gvs[consume_call_outcome_eq] >>
  qmatch_goalsub_abbrev_tac `TAKE rs rd` >>
  qmatch_goalsub_abbrev_tac `adopt_outcome rq oc triple` >>
  simp[write_memory_with_expansion_def] >>
  irule (SRULE [dse_external_update_def, write_memory_with_expansion_def, LET_THM]
    dse_external_memory_update) >> simp[]
QED

Theorem dse_exec_ext_call_ok:
  dse_local_agrees AddrSp_Memory P s t /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t /\
  exec_ext_call inst s gas addr value off sz ro rs is_static = OK s1 ==>
  ?t1. exec_ext_call inst t gas addr value off sz ro rs is_static = OK t1 /\
    dse_local_agrees AddrSp_Memory
      (FILTER (\(loc,(b,n)). ~(w2n ro <= b /\ b+n <= w2n ro+LENGTH (TAKE (w2n rs) s1.vs_returndata))) P)
      s1 t1 /\
    s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas
Proof
  strip_tac >> drule_all dse_call_request >> strip_tac >>
  qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  namedCases_on `consume_call_outcome (venom_call_request t addr value off sz is_static)
    (w2n ro) (w2n rs) s` ["output source"] >>
  simp[Excl "consume_call_outcome_eq"] >>
  strip_tac >> gvs[AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  drule_all dse_consume_call_outcome >> strip_tac >>
  simp[Excl "consume_call_outcome_eq"] >>
  irule dse_local_agrees_update_var >>
  qpat_x_assum `dse_local_agrees _ (FILTER _ _) _ _` mp_tac >>
  simp_tac bool_ss [arithmeticTheory.ADD_COMM, DE_MORGAN_THM]
QED

Theorem dse_call_memory_step:
  inst.inst_opcode IN {CALL; STATICCALL} /\
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
  `s.vs_call_ctx = t.vs_call_ctx` by
    (drule dse_local_agrees_frame >> simp[]) >>
  qpat_x_assum `step_inst _ _ _ s = _` mp_tac >>
  fs[] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
               Excl "consume_call_outcome_eq"] >>
  strip_tac >> gvs[AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  `read_memory (w2n ao) (w2n as_) s = read_memory (w2n ao) (w2n as_) t` by
    (irule dse_precise_input_bytes >>
     rpt (goal_assum (drule_at Any)) >> simp[mem_read_ops_def] >> metis_tac[]) >>
  qpat_x_assum `s.vs_call_ctx = t.vs_call_ctx`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> rewrite_tac[th]) >>
  drule_all dse_exec_ext_call_ok >> strip_tac >>
  qexistsl_tac [`t1`, `FILTER (\(loc,(b,n)).
    ~(w2n ro <= b /\ b+n <= w2n ro+LENGTH (TAKE (w2n rs) s1.vs_returndata))) P`] >>
  fs[Excl "consume_call_outcome_eq"] >>
  irule dse_pending_at_filter >> irule dse_external_pending_step >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

Theorem dse_exec_ext_call_results:
  (?s1. exec_ext_call inst s gas addr value off sz ro rs is_static = OK s1) \/
  (?e. exec_ext_call inst s gas addr value off sz ro rs is_static = Error e)
Proof
  simp[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> simp[Excl "consume_call_outcome_eq"] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `h::rest` >> Cases_on `rest` >> simp[]
QED

Theorem dse_call_results:
  inst.inst_opcode IN {CALL; STATICCALL} /\ ~s.vs_call_ctx.cc_static ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  fs[] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
    AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  rpt strip_tac >>
  gvs[exec_ext_call_def, AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> gvs[AllCaseEqs(), Excl "consume_call_outcome_eq"]
QED
