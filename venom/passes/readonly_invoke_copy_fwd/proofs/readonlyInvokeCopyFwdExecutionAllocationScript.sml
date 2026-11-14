Theory readonlyInvokeCopyFwdExecutionAllocation
Ancestors
  readonlyInvokeCopyFwdExecutionLocal readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdOpaque
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

Theorem ricf_opaque_frame_alloca_fresh[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  X SUBSET Y /\
  (!db sb sz k. (db,sb,sz) IN ricf_site_triples sites /\ k < sz ==>
    db+k < s.vs_alloca_next /\ sb+k < s.vs_alloca_next) ==>
  ricf_opaque_frame_agree fn D Y sites PG G
    (tn with t_mem := tn.t_mem UNION
      {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+z})
    (s with <|vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,z));
              vs_alloca_next := s.vs_alloca_next+z|>)
    (t with <|vs_allocas := t.vs_allocas |+ (id,(t.vs_alloca_next,z));
              vs_alloca_next := t.vs_alloca_next+z|>)
Proof
  strip_tac >>
  mp_tac (Q.INST [`D` |-> `D`, `X` |-> `X`, `Y` |-> `Y`,
    `sites` |-> `sites`, `PG` |-> `ricf_visible_params PG`,
    `G` |-> `ricf_visible_prov G`, `tn` |-> `tn`,
    `s` |-> `ricf_opaque_view fn PG G s`,
    `t` |-> `ricf_opaque_view fn PG G t`, `z` |-> `z`, `id` |-> `id`]
    ricf_frame_alloca_fresh) >>
  fs[ricf_opaque_frame_agree_def, ricf_opaque_view_def] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem ricf_opaque_stack_alloca_fresh[local]:
  ricf_opaque_live_stack_agree D ids tn maps stk targets s t /\
  (!db sb sz k j. j < LENGTH stk /\
    (db,sb,sz) IN ricf_site_triples (EL j maps) /\ k < sz ==>
      db+k < s.vs_alloca_next /\ sb+k < s.vs_alloca_next) ==>
  ricf_opaque_live_stack_agree D ids
    (tn with t_mem := tn.t_mem UNION
      {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+z}) maps stk targets
    (s with <|vs_allocas := A; vs_alloca_next := n|>)
    (t with <|vs_allocas := B; vs_alloca_next := m|>)
Proof
  strip_tac >>
  fs[ricf_opaque_live_stack_agree_def, ricf_opaque_frame_agree_def,
    ricf_opaque_view_merge, ricf_live_frame_decompose] >>
  simp[ricf_opaque_live_stack_agree_def, ricf_opaque_frame_agree_def,
    ricf_opaque_view_merge, ricf_live_frame_decompose] >>
  qx_gen_tac `j` >> strip_tac >>
  qpat_x_assum `!j. j < LENGTH stk ==> _`
    (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  `ircf_cross
    (tn with t_mem := tn.t_mem UNION
      {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+z})
    (ricf_site_triples (EL j maps))
    (s with <|vs_allocas := A; vs_alloca_next := n|>)
    (t with <|vs_allocas := B; vs_alloca_next := m|>)` by
    (irule ricf_cross_alloca_fresh >> simp[] >> metis_tac[]) >>
  mp_tac (Q.INST [`D` |-> `D`,
    `X` |-> `ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk)`,
    `sites` |-> `EL j maps`,
    `PG` |-> `ricf_visible_params
      (ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params)`,
    `G` |-> `ricf_visible_prov (EL j stk).cf_prov`,
    `tn` |-> `tn with t_mem := tn.t_mem UNION
      {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+z}`,
    `tv` |-> `(EL j stk).cf_tvar`,
    `a` |-> `ricf_opaque_view (EL j stk).cf_fn
      (ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params)
      (EL j stk).cf_prov (EL j stk).cf_state`,
    `b` |-> `ricf_opaque_view (EL j stk).cf_fn
      (ricf_complete_params (EL j stk).cf_params (EL j stk).cf_state.vs_params)
      (EL j stk).cf_prov (EL j targets)`,
    `s` |-> `s with <|vs_allocas := A; vs_alloca_next := n|>`,
    `t` |-> `t with <|vs_allocas := B; vs_alloca_next := m|>`]
    ricf_live_frame_decompose) >>
  simp[taint_fupdcanon, ld_shared_agree_def] >>
  fs[ld_shared_agree_def] >> rpt strip_tac >> metis_tac[]
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
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
   ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
     sites (ricf_complete_params PG s.vs_params) G rt s t /\
   ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) rt maps stk targets s t /\
   ircf_cross rt (ricf_phase_ranges 0 ledger) s t /\
   ricf_cert_crosses rt (ricf_phase_stack_ranges stk ledger) stk s t /\
   ricf_support_agree B E rt s t` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `occurrence_allocas_ok B a s` by
    (drule occ_frame_reachable_annotation >> simp[occurrence_annotation_ok_def]) >>
  `s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next` by
    (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >>
     drule taint_agree_allocation_fields >> simp[ricf_opaque_view_def]) >>
  `u = update_var out (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+
      (inst.inst_id,(s.vs_alloca_next,w2n amount));
      vs_alloca_next := s.vs_alloca_next+w2n amount|>)` by
    gvs[step_inst_def, step_inst_base_opcode_eqs, exec_alloca_def] >>
  `step_inst_base inst s = OK u` by gvs[step_inst_non_invoke] >>
  qabbrev_tac `us = s with <|vs_allocas := s.vs_allocas |+
    (inst.inst_id,(s.vs_alloca_next,w2n amount));
    vs_alloca_next := s.vs_alloca_next+w2n amount|>` >>
  qabbrev_tac `vt = t with <|vs_allocas := t.vs_allocas |+
    (inst.inst_id,(t.vs_alloca_next,w2n amount));
    vs_alloca_next := t.vs_alloca_next+w2n amount|>` >>
  qabbrev_tac `w = update_var out (n2w s.vs_alloca_next) vt` >>
  qabbrev_tac `un = rt with t_mem := rt.t_mem UNION
    {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+w2n amount}` >>
  `(s.vs_alloca_next,w2n amount) NOTIN FDOM sites` by
    (irule ricf_heterogeneous_alloca_map_fresh >>
     fs[ricf_execution_invariant_def] >> metis_tac[]) >>
  `!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      db+k < s.vs_alloca_next /\ sb+k < s.vs_alloca_next` by
    (match_mp_tac ricf_heterogeneous_allocation_certificate_bounds >>
     fs[ricf_execution_invariant_def] >> metis_tac[]) >>
  `ircf_dead (ricf_original_copy_ids C) s stk SUBSET
   ircf_dead (ricf_original_copy_ids C) us stk` by
    (simp[Abbr `us`] >> irule ircf_dead_allocas_mono >>
     fs[SUBMAP_FUPDATE_FLOOKUP]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) us stk)
    sites (ricf_complete_params PG s.vs_params) G un us vt` by
    (simp_tac (srw_ss()) [Abbr `us`, Abbr `vt`, Abbr `un`] >>
     irule (Q.INST [`X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`]
       ricf_opaque_frame_alloca_fresh) >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `ricf_opaque_value_agree sites (SOME (s.vs_alloca_next,w2n amount)) {}
    (if retpc_var fn out then 0w else n2w s.vs_alloca_next)
    (if retpc_var fn out then 0w else n2w s.vs_alloca_next)` by
    simp[ricf_opaque_value_agree_def, ricf_value_agree_def,
      o1LowerDloadRelocationKernelTheory.ld_value_agree_def, word_agree_except_def] >>
  drule_all ricf_opaque_frame_bind >> strip_tac >>
  `ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) un
    maps stk targets us vt` by
    (simp_tac (srw_ss()) [Abbr `un`, Abbr `us`, Abbr `vt`] >>
     irule ricf_opaque_stack_alloca_fresh >> simp[] >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!gam. _`
       (qspec_then `ricf_site_triples (EL j maps)` mp_tac) >>
     impl_tac >- metis_tac[] >>
     disch_then (qspecl_then [`db`,`sb`,`sz`,`k`] mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  `ricf_opaque_live_stack_agree D (ricf_original_copy_ids C)
    (un with t_var := set_var_taint rt.t_var [out] {}) maps stk targets
    (update_var out (n2w s.vs_alloca_next) us)
    (update_var out (n2w s.vs_alloca_next) vt)` by
    (irule ricf_opaque_live_stack_update_var >> first_assum ACCEPT_TAC) >>
  `step_prov PG G inst u =
     set_prov G [out] (SOME (s.vs_alloca_next,w2n amount)) /\
   step_taint inst s u rt =
     (rt with <|t_mem := rt.t_mem UNION
       {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next+w2n amount};
       t_var := set_var_taint rt.t_var [out] {}|>)` by
    (irule ricf_fresh_alloca_annotations >> simp[]) >>
  `ircf_cross un
    (ricf_phase_ranges 0 (ledger : (ricf_protection_event # call_frame list) list)) us vt /\
   ricf_cert_crosses un (ricf_phase_stack_ranges stk ledger) stk us vt` by
    (simp[ricf_cert_crosses_def, Abbr `un`, Abbr `us`, Abbr `vt`] >>
     conj_tac
     >- (irule ricf_cross_alloca_fresh >> simp[] >>
         qpat_x_assum `!gam. _`
           (qspec_then `ricf_phase_ranges 0 ledger` mp_tac) >>
         simp[arithmeticTheory.ADD_COMM]) >>
     fs[ricf_cert_crosses_def, EVERY_MEM] >> rpt strip_tac >>
     irule ricf_cross_alloca_fresh >> fs[EVERY_MEM] >>
     qpat_x_assum `!gam. _` (qspec_then `gam` mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  `(a,inst.inst_id) NOTIN E` by
    (irule ricf_heterogeneous_alloca_support_fresh >>
     fs[ricf_execution_invariant_def] >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas inst.inst_id = NONE` by metis_tac[] >>
  `step_inst_base inst t = OK w` by
    simp[Abbr `w`, Abbr `vt`, step_inst_base_opcode_eqs, exec_alloca_def] >>
  `ricf_support_agree (occurrence_sites_step a B inst u) E
    (step_taint inst s u rt) u w` by
    (drule_all ricf_support_actual_fresh_alloca >> strip_tac >>
     gvs[ricf_support_agree_def, Abbr `w`, Abbr `vt`] >> first_assum ACCEPT_TAC) >>
  `step_inst fuel Ct inst t = OK w` by
    fs[step_inst_non_invoke] >>
  `ircf_cross (step_taint inst s u rt) (ricf_phase_ranges 0 ledger) u w /\
   ricf_cert_crosses (step_taint inst s u rt)
     (ricf_phase_stack_ranges stk ledger) stk u w` by
    (qpat_assum `step_taint inst s u rt = _` (fn th => REWRITE_TAC [th]) >>
     qpat_assum `u = update_var out _ us` (fn th => REWRITE_TAC [th]) >>
     qpat_x_assum `ircf_cross un _ us vt` mp_tac >>
     qpat_x_assum `ricf_cert_crosses un _ stk us vt` mp_tac >>
     simp_tac (srw_ss()) [Abbr `us`, Abbr `vt`, Abbr `w`, Abbr `un`,
       update_var_def, ircf_cross_def, ricf_cert_crosses_def]) >>
  qexists_tac `w` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule ricf_execution_next >>
  simp[is_terminator_def] >>
  `u = update_var out (n2w s.vs_alloca_next) us` by simp[Abbr `us`] >>
  rpt conj_tac
  >- (qexists_tac `fuel` >> simp[]) >>
  gvs[Abbr `us`, Abbr `vt`, Abbr `w`, Abbr `un`, ircf_dead_def, update_var_def] >>
  qexists_tac `t` >> first_assum ACCEPT_TAC
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
   ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk) sites
     (ricf_complete_params PG s.vs_params) G rt s t` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `(b,z) NOTIN FDOM sites` by metis_tac[ricf_heterogeneous_cached_alloca_map_exclusion] >>
  `s.vs_allocas = t.vs_allocas` by
    (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >>
     drule taint_agree_allocation_fields >> simp[ricf_opaque_view_def]) >>
  `occurrence_allocas_ok B a s` by
    (drule occ_frame_reachable_annotation >> simp[occurrence_annotation_ok_def]) >>
  `u = update_var out (n2w b) s` by
    gvs[step_inst_def, step_inst_base_opcode_eqs, exec_alloca_def] >>
  `step_inst fuel Ct inst t = OK (update_var out (n2w b) t)` by
    gvs[step_inst_def, step_inst_base_opcode_eqs, exec_alloca_def] >>
  `ricf_opaque_value_agree sites (SOME (b,z)) {}
    (if retpc_var fn out then 0w else n2w b)
    (if retpc_var fn out then 0w else n2w b)` by
    simp[ricf_opaque_value_agree_def, ricf_value_agree_def,
      ld_value_agree_def, word_agree_except_def,
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
