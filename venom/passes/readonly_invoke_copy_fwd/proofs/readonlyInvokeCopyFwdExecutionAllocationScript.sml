Theory readonlyInvokeCopyFwdExecutionAllocation
Ancestors
  readonlyInvokeCopyFwdExecutionLocal readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdOperationalAllocation readonlyInvokeCopyFwdOperationalGuards
  readonlyInvokeCopyFwdHeterogeneousAllocation readonlyInvokeCopyFwdHeterogeneousSupport
  readonlyInvokeCopyFwdHeterogeneousMapOrigins
  readonlyInvokeCopyFwdStepsAllocation readonlyInvokeCopyFwdStepsCore
  readonlyInvokeCopyFwdGlobalSupport readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdOperationalMapOrigins readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdCalls
  readonlyInvokeCopyFwdHistoryPhase internalReturnCopyFwdSim
  o1LowerDloadOccurrence o1LowerDloadShared occurrenceGeometry
  o1LowerDloadRelocationKernel taintAgree ptrDiscipline
  venomExecSemantics venomState venomInst finite_map list pred_set words

Theorem ricf_fresh_alloca_annotations[local]:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit amount] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  u = update_var out (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+
      (inst.inst_id,(s.vs_alloca_next,w2n amount));
      vs_alloca_next := s.vs_alloca_next+w2n amount|>) ==>
  step_prov PG G inst u =
    set_prov G [out] (SOME (s.vs_alloca_next,w2n amount)) /\
  step_taint inst s u rt =
    (rt with <|t_mem := rt.t_mem UNION
       {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+w2n amount};
       t_var := set_var_taint rt.t_var [out] {}|>)
Proof
  strip_tac >>
  `new_site_bytes s u =
    {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+w2n amount}` by
    (gvs[new_site_bytes_def, update_var_def] >>
     simp[EXTENSION, FLOOKUP_UPDATE] >> gen_tac >> eq_tac
     >- (strip_tac >> Cases_on `inst.inst_id = aid` >> gvs[FLOOKUP_DEF]) >>
     strip_tac >> qexistsl_tac [`inst.inst_id`,`s.vs_alloca_next`,`w2n amount`] >>
     fs[FLOOKUP_DEF]) >>
  gvs[step_prov_def, out_prov_def, step_taint_def, out_taint_def,
    mem_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
    step_writes_def, written_taint_def, range_bytes_def,
    codegenRelTheory.source_memory_write_ranges_def, update_var_def,
    FLOOKUP_UPDATE, eval_operand_def, taint_component_equality]
QED

Theorem ricf_execution_fresh_alloca_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  occurrence_natural_geometry lo a U B stk s /\
  active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit amount] /\ inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u rt)
Proof
  pure_rewrite_tac[ricf_execution_invariant_def] >> strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `step_inst_base inst s = OK u` by fs[step_inst_non_invoke] >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_heterogeneous_source_ledger_def] >>
  `occurrence_allocas_ok B a s` by
    (drule occ_frame_reachable_annotation >> simp[occurrence_annotation_ok_def]) >>
  `u = update_var out (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+
      (inst.inst_id,(s.vs_alloca_next,w2n amount));
      vs_alloca_next := s.vs_alloca_next+w2n amount|>)` by
    gvs[step_inst_def, step_inst_base_opcode_eqs, exec_alloca_def] >>
  `ricf_cert_core D (ricf_original_copy_ids C) stk PG
    (ricf_effective_prov fn s G) (ricf_effective_taint fn s rt) fn
    sites maps targets G rt (ricf_phase_ranges 0 ledger)
    (ricf_phase_stack_ranges stk ledger) s t` by
    (irule ricf_cert_reconstruct >> simp[]) >>
  `(s.vs_alloca_next,w2n amount) NOTIN FDOM sites` by
    metis_tac[ricf_heterogeneous_alloca_map_fresh] >>
  `!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      db+k < s.vs_alloca_next /\ sb+k < s.vs_alloca_next` by
    (match_mp_tac ricf_heterogeneous_allocation_certificate_bounds >> metis_tac[]) >>
  `?w. step_inst_base inst t = OK w /\
    ricf_cert_core D (ricf_original_copy_ids C) stk PG
      (ricf_effective_prov fn u (set_prov G [out]
        (SOME (s.vs_alloca_next,w2n amount))))
      (ricf_effective_taint fn u
        (rt with <|t_mem := rt.t_mem UNION
          {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+w2n amount};
          t_var := set_var_taint rt.t_var [out] {}|>)) fn
      sites maps targets (set_prov G [out] (SOME (s.vs_alloca_next,w2n amount)))
      (rt with <|t_mem := rt.t_mem UNION
          {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+w2n amount};
          t_var := set_var_taint rt.t_var [out] {}|>)
      (ricf_phase_ranges 0 ledger) (ricf_phase_stack_ranges stk ledger) u w` by
    (mp_tac (Q.INST
       [`G` |-> `ricf_effective_prov fn s G`,
        `tn` |-> `ricf_effective_taint fn s rt`,
        `G0` |-> `G`, `tn0` |-> `rt`,
        `ids` |-> `ricf_original_copy_ids C`,
        `cur` |-> `ricf_phase_ranges 0
          (ledger:(ricf_protection_event # call_frame list) list)`,
        `curs` |-> `ricf_phase_stack_ranges stk
          (ledger:(ricf_protection_event # call_frame list) list)`,
        `u` |-> `s with <|vs_allocas := s.vs_allocas |+
          (inst.inst_id,(s.vs_alloca_next,w2n amount));
          vs_alloca_next := s.vs_alloca_next+w2n amount|>`,
        `v` |-> `t with <|vs_allocas := t.vs_allocas |+
          (inst.inst_id,(t.vs_alloca_next,w2n amount));
          vs_alloca_next := t.vs_alloca_next+w2n amount|>`,
        `un` |-> `rt with t_mem := rt.t_mem UNION
          {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+w2n amount}`]
       ricf_cert_alloca_fresh) >> impl_tac
     >- (simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     strip_tac >>
     qexists_tac `update_var out (n2w s.vs_alloca_next)
       (t with <|vs_allocas := t.vs_allocas |+
         (inst.inst_id,(t.vs_alloca_next,w2n amount));
         vs_alloca_next := t.vs_alloca_next+w2n amount|>)` >> gvs[]) >>
  `step_prov PG G inst u =
     set_prov G [out] (SOME (s.vs_alloca_next,w2n amount)) /\
   step_taint inst s u rt =
     (rt with <|t_mem := rt.t_mem UNION
       {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+w2n amount};
       t_var := set_var_taint rt.t_var [out] {}|>)` by
    (irule ricf_fresh_alloca_annotations >> simp[]) >>
  `ricf_heterogeneous_source_ledger vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    n a U (occurrence_sites_step a B inst u) HP
    (occurrence_step a HP H inst u) ledger` by
    (irule ricf_heterogeneous_source_ledger_actual_next >> metis_tac[]) >>
  `ricf_heterogeneous_map_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U B sites` by (irule ricf_heterogeneous_map_origins_next >> metis_tac[]) >>
  `ricf_heterogeneous_map_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U (occurrence_sites_step a B inst u) sites` by
    metis_tac[ricf_heterogeneous_map_origins_sites_step] >>
  `ricf_heterogeneous_saved_map_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U B maps` by (irule ricf_heterogeneous_saved_map_origins_next >> metis_tac[]) >>
  `ricf_heterogeneous_saved_map_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U (occurrence_sites_step a B inst u) maps` by
    metis_tac[ricf_heterogeneous_saved_map_origins_sites_step] >>
  `ricf_heterogeneous_support_origins vs C a fn U stk
    (occurrence_sites_step a B inst u) E` by
    (irule ricf_heterogeneous_support_actual_next >> metis_tac[]) >>
  `s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next` by
    (fs[ricf_frame_agree_def] >> drule taint_agree_allocation_fields >> simp[]) >>
  `(a,inst.inst_id) NOTIN E` by metis_tac[ricf_heterogeneous_alloca_support_fresh] >>
  `ricf_support_agree (occurrence_sites_step a B inst u) E
    (step_taint inst s u rt) u w` by
    (drule_all ricf_support_actual_fresh_alloca >> strip_tac >>
     gvs[ricf_support_agree_def]) >>
  qpat_x_assum `u = update_var _ _ _` (K ALL_TAC) >>
  qexists_tac `w` >> simp[step_inst_non_invoke] >>
  fs[ricf_cert_core_def, ricf_live_boundary_core_def] >>
  conj_tac >-
    (qpat_assum `ricf_frame_agree _ _ _ _ _ _ u w`
       (mp_then Any (qspec_then `SUC s.vs_inst_idx` mp_tac) ricf_frame_inst_idx) >>
     simp[ircf_dead_def]) >>
  fs[ricf_live_stack_agree_def, ricf_cert_crosses_def, ircf_cross_def,
    ricf_support_agree_def, merge_callee_state_def] >>
  simp[ricf_live_stack_agree_def, ricf_cert_crosses_def, ircf_cross_def,
    ricf_support_agree_def, merge_callee_state_def] >>
  first_assum ACCEPT_TAC
QED

Theorem ricf_execution_cached_alloca_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  occurrence_natural_geometry lo a U B stk s /\
  active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit amount] /\ inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,z) /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u rt)
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
   ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B sites /\
   ricf_frame_agree D (ircf_dead (ricf_original_copy_ids C) s stk) sites
     (ricf_complete_params PG s.vs_params) G rt s t` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `(b,z) NOTIN FDOM sites` by metis_tac[ricf_heterogeneous_cached_alloca_map_exclusion] >>
  `s.vs_allocas = t.vs_allocas` by
    (fs[ricf_frame_agree_def] >> drule taint_agree_allocation_fields >> simp[]) >>
  `occurrence_allocas_ok B a s` by
    (drule occ_frame_reachable_annotation >> simp[occurrence_annotation_ok_def]) >>
  `u = update_var out (n2w b) s` by
    gvs[step_inst_def, step_inst_base_opcode_eqs, exec_alloca_def] >>
  `step_inst fuel Ct inst t = OK (update_var out (n2w b) t)` by
    gvs[step_inst_def, step_inst_base_opcode_eqs, exec_alloca_def] >>
  `ricf_value_agree sites (SOME (b,z)) {} (n2w b) (n2w b)` by
    simp[ricf_value_agree_def, ld_value_agree_def, word_agree_except_def,
      GSYM FLOOKUP_DEF] >>
  `FLOOKUP t.vs_allocas inst.inst_id = SOME (b,z)` by metis_tac[] >>
  `FLOOKUP B (a,inst.inst_id) = SOME (b,z)` by
    fs[occurrence_allocas_ok_def] >>
  `B |+ ((a,inst.inst_id),(b,z)) = B` by
    (irule FUPDATE_ELIM >> fs[FLOOKUP_DEF]) >>
  `occurrence_sites_step a B inst (update_var out (n2w b) s) = B` by
    simp[occurrence_sites_step_def, update_var_def] >>
  `new_site_bytes s (update_var out (n2w b) s) = {}` by
    (simp[new_site_bytes_def, update_var_def, EXTENSION, FLOOKUP_DEF] >>
     metis_tac[]) >>
  qpat_x_assum `u = update_var _ _ _` SUBST_ALL_TAC >>
  qexists_tac `update_var out (n2w b) t` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  match_mp_tac (Q.INST [`p` |-> `SOME (b,z)`, `m` |-> `{}`]
    ricf_execution_bind_next) >>
  simp[step_prov_def, out_prov_def, step_taint_def, out_taint_def,
    mem_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
    step_writes_def, written_taint_def, range_bytes_def,
    taint_component_equality,
    codegenRelTheory.source_memory_write_ranges_def,
    eval_operand_def, is_terminator_def, SF CONJ_ss] >>
  gvs[update_var_def, new_site_bytes_def, EXTENSION, FLOOKUP_DEF]
QED
