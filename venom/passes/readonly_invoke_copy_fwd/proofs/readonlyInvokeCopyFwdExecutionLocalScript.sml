Theory readonlyInvokeCopyFwdExecutionLocal
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdValues readonlyInvokeCopyFwdCalls
  readonlyInvokeCopyFwdSteps readonlyInvokeCopyFwdOperationalGuards
  readonlyInvokeCopyFwdGlobalSupport readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdOperationalMapOrigins readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdHistoryPhase
  internalReturnCopyFwdSim o1LowerDloadShared o1LowerDloadOccurrence
  taintAgree ptrDiscipline venomExecSemantics venomState venomInst finite_map list pred_set

Theorem ricf_execution_bind_next:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK (update_var out x s) /\
  step_inst fuel Ct inst t = OK (update_var out y t) /\
  active_inst fn next ((update_var out x s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  ricf_value_agree sites p m x y /\
  step_prov PG G inst (update_var out x s) = set_prov G [out] p /\
  step_taint inst s (update_var out x s) rt =
    (rt with t_var := set_var_taint rt.t_var [out] m) /\
  occurrence_sites_step a B inst (update_var out x s) = B ==>
  ricf_execution_invariant vs C ctx0 log D stk PG
    (step_prov PG G inst (update_var out x s))
    (step_taint inst s (update_var out x s) tn) fn next
    ((update_var out x s) with vs_inst_idx := SUC s.vs_inst_idx)
    ((update_var out y t) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U (occurrence_sites_step a B inst (update_var out x s)) HP
    (occurrence_step a HP H inst (update_var out x s)) ledger E sites maps targets
    (step_taint inst s (update_var out x s) rt)
Proof
  pure_rewrite_tac[ricf_execution_invariant_def] >> strip_tac >>
  drule_all ricf_bind_live >> disch_then (qspec_then `out` strip_assume_tac) >>
  `ricf_heterogeneous_source_ledger vs C stk PG
    (step_prov PG G inst (update_var out x s))
    (step_taint inst s (update_var out x s) tn) fn next
    ((update_var out x s) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U (occurrence_sites_step a B inst (update_var out x s)) HP
    (occurrence_step a HP H inst (update_var out x s)) ledger` by
    (irule ricf_heterogeneous_source_ledger_actual_next >> metis_tac[]) >>
  `ricf_map_origins vs C ctx0 log stk PG
    (step_prov PG G inst (update_var out x s))
    (step_taint inst s (update_var out x s) tn) fn next
    ((update_var out x s) with vs_inst_idx := SUC s.vs_inst_idx)
    U B sites` by (irule ricf_map_origins_next >> metis_tac[]) >>
  `ricf_global_support_origins vs C ctx0 a fn U stk B E` by
    metis_tac[] >>
  simp[Once ircf_dead_def, update_var_def] >>
  conj_tac >-
    (qpat_assum `ricf_frame_agree _ _ _ _ (set_prov _ _ _) _ _ _`
       (mp_then Any (qspec_then `SUC s.vs_inst_idx` mp_tac) ricf_frame_inst_idx) >>
     simp[ircf_dead_def, update_var_def]) >>
  conj_tac >-
    (qpat_x_assum `ricf_live_stack_agree _ _ (_ with t_var := _) _ _ _ _ _` mp_tac >>
     simp[ricf_live_stack_agree_def, merge_callee_state_def, update_var_def]) >>
  conj_tac >-
    (qpat_x_assum `ircf_cross _ _ _ _` mp_tac >> simp[ircf_cross_def, update_var_def]) >>
  conj_tac >-
    (qpat_x_assum `ricf_cert_crosses _ _ _ _ _` mp_tac >>
     simp[ricf_cert_crosses_def, ircf_cross_def, merge_callee_state_def, update_var_def]) >>
  qpat_x_assum `ricf_support_agree _ _ _ _ _` mp_tac >>
  simp[ricf_support_agree_def, update_var_def] >>
  gvs[update_var_def]
QED

Theorem ricf_execution_param_next:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = PARAM /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C ctx0 log D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u rt)
Proof
  strip_tac >>
  `w2n idx < LENGTH s.vs_params /\
   u = update_var out (EL (w2n idx) s.vs_params) s` by
    gvs[step_inst_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  `ricf_frame_agree D (ircf_dead (ricf_original_copy_ids C) s stk) sites
    (ricf_complete_params PG s.vs_params) G rt s t` by
    fs[ricf_execution_invariant_def] >>
  `ricf_params_agree sites (ricf_complete_params PG s.vs_params)
    s.vs_params t.vs_params` by metis_tac[ricf_frame_agree_params] >>
  `LENGTH PG <= LENGTH s.vs_params` by
    (fs[ricf_params_agree_def, ricf_complete_params_def] >> decide_tac) >>
  `ricf_value_agree sites
    (if w2n idx < LENGTH PG then EL (w2n idx) PG else NONE) {}
    (EL (w2n idx) s.vs_params) (EL (w2n idx) t.vs_params)` by
    (drule_all ricf_frame_agree_param >>
     simp[ricf_complete_params_el]) >>
  qexists_tac `update_var out (EL (w2n idx) t.vs_params) t` >>
  conj_asm1_tac >-
    gvs[step_inst_def, step_inst_base_opcode_eqs, ricf_params_agree_def] >>
  gvs[] >> irule ricf_execution_bind_next >>
  simp[step_prov_def, out_prov_def, step_taint_def,
    out_taint_def, mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, taint_component_equality, occurrence_sites_step_def,
    codegenRelTheory.source_memory_write_ranges_def, update_var_def,
    FLOOKUP_DEF, eval_operand_def, is_terminator_def, SF CONJ_ss] >>
  metis_tac[update_var_def]
QED

Theorem ricf_execution_nop_next:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = NOP /\ inst.inst_outputs = [] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C ctx0 log D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u rt)
Proof
  pure_rewrite_tac[ricf_execution_invariant_def] >> strip_tac >>
  `u = s` by gvs[step_inst_def, step_inst_base_opcode_eqs] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `ricf_heterogeneous_source_ledger vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    n a U (occurrence_sites_step a B inst u) HP
    (occurrence_step a HP H inst u) ledger` by
    (irule ricf_heterogeneous_source_ledger_actual_next >> metis_tac[]) >>
  `ricf_map_origins vs C ctx0 log stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U B sites` by (irule ricf_map_origins_next >> metis_tac[]) >>
  `written_taint rt inst s = {} /\ written_taint tn inst s = {}` by
    (simp[written_taint_def] >> rpt CASE_TAC >> simp[]) >>
  qexists_tac `t` >> simp[step_inst_def, step_inst_base_opcode_eqs] >>
  `<|t_mem := tn.t_mem; t_var := tn.t_var; t_stor := tn.t_stor;
      t_trans := tn.t_trans; t_imm := tn.t_imm|> = tn` by
    simp[taint_component_equality] >>
  `<|t_mem := rt.t_mem; t_var := rt.t_var; t_stor := rt.t_stor;
      t_trans := rt.t_trans; t_imm := rt.t_imm|> = rt` by
    simp[taint_component_equality] >>
  gvs[step_prov_def, set_prov_def, step_taint_def, set_var_taint_def,
    DRESTRICT_UNIV,
    mem_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
    new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def,
    occurrence_sites_step_def,
    codegenRelTheory.source_memory_write_ranges_def, FLOOKUP_DEF, SF CONJ_ss] >>
  conj_tac >-
    (drule ricf_frame_inst_idx >>
     disch_then (qspec_then `SUC s.vs_inst_idx` mp_tac) >> simp[ircf_dead_def]) >>
  simp[ricf_live_stack_agree_def, merge_callee_state_def,
    ircf_cross_def, ricf_cert_crosses_def, ricf_support_agree_def] >>
  gvs[ricf_live_stack_agree_def, merge_callee_state_def,
    ircf_cross_def, ricf_cert_crosses_def, ricf_support_agree_def] >>
  first_assum ACCEPT_TAC
QED
