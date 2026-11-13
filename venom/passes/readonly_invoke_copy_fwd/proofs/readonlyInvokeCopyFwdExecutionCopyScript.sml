Theory readonlyInvokeCopyFwdExecutionCopy
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdCopyFrontier
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdHeterogeneousSupport
  readonlyInvokeCopyFwdHeterogeneousMapOrigins frameViewFacts frameRel
  readonlyInvokeCopyFwdMemory readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdOperationalGuards readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdOperationalMapOrigins readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdCalls readonlyInvokeCopyFwdGlobalSupport
  readonlyInvokeCopyFwdLedgerActivation readonlyInvokeCopyFwdMapCopyGuards
  readonlyInvokeCopyFwdHistoryAvailability readonlyInvokeCopyFwdHistoryVisitAccess
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdHistoryReadExceptions readonlyInvokeCopyFwdProtectionOrigin
  occurrenceGeometry occurrenceOrigin venomWf venomWfProps o1PassContract
  mem2varProofs contextCodegenRel readonlyInvokeCopyFwdOperationalPositiveCopy
  readonlyInvokeCopyFwdSupportSeparation readonlyInvokeCopyFwdHistory
  readonlyInvokeCopyFwdPlan
  internalReturnCopyFwdSim o1LowerDloadOccurrence o1LowerDloadShared
  ptrDiscipline taintAgree venomExecSemantics venomState venomInst
  finite_map list pred_set words arithmetic

Theorem ricf_opaque_frame_source_mcopy_frontier[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  {i | db <= i /\ i < db+len /\ i < s.vs_alloca_next} SUBSET X /\
  (db+len <= sb \/ sb+len <= db) /\
  (!q. q < len /\ sb+q NOTIN tn.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory) /\
  tn' = tn with t_mem :=
    (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
    {db+q | q < len /\ sb+q IN tn.t_mem} /\
  (!b c z k. (b,c,z) IN ricf_site_triples sites /\ k < z ==>
    ~(db <= b+k /\ b+k < db+len) /\
    ~(db <= c+k /\ c+k < db+len)) ==>
  ricf_opaque_frame_agree fn D X sites PG G tn' (mcopy db sb len s) t
Proof
  pure_rewrite_tac[ricf_opaque_frame_agree_def] >> strip_tac >>
  `ricf_opaque_view fn PG G (mcopy db sb len s) =
   mcopy db sb len (ricf_opaque_view fn PG G s)` by
    simp[ricf_opaque_view_def, mcopy_def,
      write_memory_with_expansion_def] >>
  `(ricf_opaque_view fn PG G s).vs_alloca_next = s.vs_alloca_next /\
   (ricf_opaque_view fn PG G s).vs_memory = s.vs_memory /\
   (ricf_opaque_view fn PG G t).vs_memory = t.vs_memory` by
    simp[ricf_opaque_view_def] >>
  simp[] >>
  match_mp_tac (ricf_frame_source_mcopy_frontier |> Q.INST [`tn` |-> `tn`]) >>
  asm_simp_tac (srw_ss()) [ADD_COMM] >> metis_tac[ADD_COMM]
QED

Theorem ricf_opaque_live_stack_source_mcopy_frontier[local]:
  ricf_opaque_live_stack_agree D ids tn maps stk targets s t /\
  (!j i. j < LENGTH stk /\ db <= i /\ i < db+len /\
    i < (EL j stk).cf_state.vs_alloca_next ==>
    i IN ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk)) /\
  (db+len <= sb \/ sb+len <= db) /\
  (!q. q < len /\ sb+q NOTIN tn.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory) /\
  tn' = tn with t_mem :=
    (tn.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
    {db+q | q < len /\ sb+q IN tn.t_mem} /\
  (!j b c z k. j < LENGTH stk /\
    (b,c,z) IN ricf_site_triples (EL j maps) /\ k < z ==>
    ~(db <= b+k /\ b+k < db+len) /\
    ~(db <= c+k /\ c+k < db+len)) ==>
  ricf_opaque_live_stack_agree D ids tn' maps stk targets (mcopy db sb len s) t
Proof
  pure_rewrite_tac [ricf_opaque_live_stack_agree_def, ricf_mcopy_merge] >>
  strip_tac >> asm_rewrite_tac[] >> gen_tac >> strip_tac >>
  match_mp_tac (ricf_opaque_frame_source_mcopy_frontier |> Q.INST
    [`tn` |-> `tn with t_var := (EL j stk).cf_tvar`]) >>
  asm_simp_tac (srw_ss()) [merge_callee_state_def, SUBSET_DEF] >>
  metis_tac[ADD_COMM]
QED

Theorem ricf_execution_zero_copy_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = MCOPY /\
  inst.inst_operands = [dop;rop;Lit 0w] /\ inst.inst_outputs = [] /\
  step_inst fuel C inst s = OK u /\
  nop.inst_opcode = NOP /\ nop.inst_operands = [] /\ nop.inst_outputs = [] /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  step_inst fuel Ct nop t = OK t /\
  ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx)
    (t with vs_inst_idx := SUC s.vs_inst_idx)
    n a U (occurrence_sites_step a B inst u) HP
    (occurrence_step a HP H inst u) ledger E sites maps targets
    (step_taint inst s u rt)
Proof
  pure_rewrite_tac[ricf_execution_invariant_def] >> strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `?d r. eval_operand dop s = SOME d /\ eval_operand rop s = SOME r /\
    u = mcopy (w2n d) (w2n r) 0 s` by
    gvs[step_inst_def, step_inst_base_opcode_eqs, eval_operand_def,
      AllCaseEqs()] >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `step_prov PG G inst u = G /\ step_taint inst s u tn = tn /\
    step_taint inst s u rt = rt /\ occurrence_sites_step a B inst u = B /\
    occurrence_step a HP H inst u = H` by
    (simp[step_prov_def, occurrence_sites_step_def, occurrence_step_def,
       set_prov_def, DRESTRICT_UNIV] >>
     `!T. step_taint inst s u T = T` suffices_by simp[] >>
     gen_tac >> drule_all step_taint_mcopy >> simp[EXTENSION]) >>
  `ricf_heterogeneous_source_ledger vs C stk PG G tn fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H ledger` by
    (drule_all ricf_heterogeneous_source_ledger_actual_next >> simp[]) >>
  `ricf_heterogeneous_map_origins vs C stk PG G tn fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx) U B sites` by
    (drule_all ricf_heterogeneous_map_origins_next >> simp[]) >>
  `ricf_heterogeneous_saved_map_origins vs C stk PG G tn fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx) U B maps` by
    (drule_all ricf_heterogeneous_saved_map_origins_next >> simp[]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G rt u t` by
    (simp[] >> irule ricf_opaque_frame_source_mcopy_frontier >>
     simp[SUBSET_DEF, EXTENSION] >> metis_tac[LESS_EQ_CASES]) >>
  `ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) rt maps stk targets u t` by
    (simp[] >> irule ricf_opaque_live_stack_source_mcopy_frontier >>
     simp[EXTENSION] >> metis_tac[LESS_EQ_CASES]) >>
  `ircf_cross rt (ricf_phase_ranges 0 ledger) u t` by
    (simp[] >> irule ricf_cross_source_mcopy_frame >>
     simp[EXTENSION] >> metis_tac[LESS_EQ_CASES]) >>
  `ricf_cert_crosses rt (ricf_phase_stack_ranges stk ledger) stk u t` by
    (fs[ricf_cert_crosses_def, EVERY_MEM] >>
     simp[ricf_cert_crosses_def, EVERY_MEM] >> rpt strip_tac >>
     simp[] >>
     irule ricf_cross_source_mcopy_frame >>
     simp[EXTENSION] >> metis_tac[LESS_EQ_CASES]) >>
  `ricf_support_agree B E rt u t` by metis_tac[ricf_support_zero_copy] >>
  simp[step_inst_def, step_inst_base_opcode_eqs] >>
  gvs[ircf_dead_def, mcopy_def, write_memory_with_expansion_def] >>
  conj_tac
  >- (qpat_assum `ricf_opaque_frame_agree fn _ _ _ _ _ _ (_ with vs_memory := _) _`
        (mp_then Any (qspec_then `SUC s.vs_inst_idx` mp_tac) ricf_opaque_frame_inst_idx) >>
      simp[ircf_dead_def]) >>
  conj_tac
  >- fs[ricf_opaque_live_stack_agree_def, ricf_opaque_frame_agree_def,
       ricf_opaque_view_def, merge_callee_state_def] >>
  conj_tac >-
    (qpat_x_assum `ircf_cross _ _ (_ with vs_memory := _) _` mp_tac >>
     simp[ircf_cross_def]) >>
  conj_tac >-
    (qpat_x_assum `ricf_cert_crosses _ _ _ (_ with vs_memory := _) _` mp_tac >>
     simp[ricf_cert_crosses_def, ircf_cross_def, merge_callee_state_def]) >>
  qpat_x_assum `ricf_support_agree _ _ _ (_ with vs_memory := _) _` mp_tac >>
  simp[ricf_support_agree_def]
QED

Theorem ricf_execution_positive_copy_next:
  ricf_execution_invariant vs C D stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s t
    n a U B HP H ledger E sites maps targets rt /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ssa_form fn /\ wf_function fn /\ fn_inst_wf fn /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;Lit z] /\
  0 < w2n z /\ occurrence_natural_geometry lo a U B stk s /\
  s.vs_alloca_next <= dimword (:256) /\
  active_inst fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\
  access_ok lo G fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\
  ~in_revert_forward fn s /\
  step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  nop.inst_opcode = NOP /\ nop.inst_operands = [] /\ nop.inst_outputs = [] ==>
  ?p ledger'.
    p.rpe_event = e /\ p.rpe_block = EL b fn.fn_blocks /\ p.rpe_fn = fn /\
    p.rpe_before = s /\ p.rpe_after = u /\ p.rpe_owner = a /\
    ricf_history_origin vs C ctx0 log p stk PG G tn /\
    ledger' = (p,[])::ledger /\
    step_inst fuel Ct nop t = OK t /\
    ricf_execution_invariant vs C D stk PG
      (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
      (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (t with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B (ricf_event_copy e (EL b fn.fn_blocks)) u) HP
      (occurrence_step a HP H (ricf_event_copy e (EL b fn.fn_blocks)) u)
      ledger' (E UNION {p.rpe_dst}) sites maps targets
      (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u rt)
Proof
  pure_rewrite_tac[ricf_execution_invariant_def] >> strip_tac >>
  qpat_assum `ricf_heterogeneous_source_ledger _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ricf_heterogeneous_source_ledger_def]) >>
  drule_all ricf_located_event_operands_available >> strip_tac >> gvs[] >>
  qabbrev_tac `u = mcopy (db MOD dimword (:256)) (sb MOD dimword (:256)) (w2n z) s` >>
  `MEM fn C.ctx_functions` by metis_tac[occ_frame_reachable_annotation] >>
  `MEM (EL b fn.fn_blocks) fn.fn_blocks /\
   e.rfe_index < LENGTH (EL b fn.fn_blocks).bb_instructions` by
    (drule_all ricf_located_event_source_block >> strip_tac >>
     drule_all ricf_located_event_source_descriptor >> strip_tac >>
     drule ricf_located_event_validation >> strip_tac >>
     drule ricf_event_copy_shape >> strip_tac >>
     fs[ricf_block_edit_def] >> metis_tac[EL_MEM, LIST_REL_LENGTH]) >>
  `MEM (ricf_event_copy e (EL b fn.fn_blocks)) (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `(ricf_event_copy e (EL b fn.fn_blocks)).inst_outputs = []` by
    (`inst_wf (ricf_event_copy e (EL b fn.fn_blocks))` by
       (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
     gvs[inst_wf_def]) >>
  `da.inst_id IN ricf_original_copy_ids C` by
    (simp[ricf_original_copy_ids_def] >> metis_tac[]) >>
  `da.inst_id <> sa.inst_id` by
    (strip_tac >>
     `da = sa` by
       (irule (Q.ISPEC `\i:instruction. i.inst_id` ALL_DISTINCT_MAP_IMP) >>
        simp[] >> qexists_tac `fn_insts fn` >> simp[]) >>
     `dr = sv` by gvs[] >>
     drule_all ricf_located_event_original_destination_alloca >> strip_tac >>
     drule ricf_source_copy_not_destination >>
     fs[ricf_event_copy_def] >> metis_tac[]) >>
  `db+w2n z <= s.vs_alloca_next /\ sb+w2n z <= s.vs_alloca_next` by
    metis_tac[occurrence_geometry_site_bounds] >>
  `db < dimword (:256) /\ sb < dimword (:256)` by decide_tac >>
  (Q.SUBGOAL_THEN `db+w2n z <= sb \/ sb+w2n z <= db` ASSUME_TAC >-
    metis_tac[occurrence_geometry_sites_disjoint, pairTheory.PAIR_EQ]) >>
  `u = mcopy db sb (w2n z) s` by simp[Abbr `u`] >>
  `!q. q < w2n z /\ sb+q NOTIN rt.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory` by
    (drule_all ricf_located_event_original_destination_alloca >> strip_tac >>
     drule_all ricf_heterogeneous_source_support_separation >> strip_tac >>
     metis_tac[ricf_support_separated_source_agree]) >>
  `!x y w k. (x,y,w) IN ricf_site_triples sites /\ k < w ==>
    ~(db <= x+k /\ x+k < db+w2n z) /\
    ~(db <= y+k /\ y+k < db+w2n z)` by
    metis_tac[ricf_heterogeneous_map_origins_current_copy_exclusion, pairTheory.FST] >>
  `!j x y w k. j < LENGTH stk /\
    (x,y,w) IN ricf_site_triples (EL j maps) /\ k < w ==>
    ~(db <= x+k /\ x+k < db+w2n z) /\
    ~(db <= y+k /\ y+k < db+w2n z)` by
    metis_tac[ricf_heterogeneous_saved_map_origins_current_copy_exclusion, pairTheory.FST] >>
  `{i | db <= i /\ i < db+w2n z} SUBSET
    ircf_dead (ricf_original_copy_ids C) s stk` by
    (simp[SUBSET_DEF, ircf_dead_def, site_bytes_def] >> metis_tac[]) >>
  `!j i. j < LENGTH stk /\ db <= i /\ i < db+w2n z /\
    i < (EL j stk).cf_state.vs_alloca_next ==>
    i IN ircf_dead (ricf_original_copy_ids C) (EL j stk).cf_state (DROP (SUC j) stk)` by
    metis_tac[ricf_copy_saved_observer_geometry, pairTheory.FST] >>
  `occurrence_syntax_origin fn a H` by
    metis_tac[occ_frame_reachable_origin_certificate,
              occurrence_origin_certificate_current] >>
  `!gam x y w k.
    (gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger)) /\ (x,y,w) IN gam /\ k < w ==>
    ~(db <= x+k /\ x+k < db+w2n z) /\
    ~(db <= y+k /\ y+k < db+w2n z)` by
    (drule ricf_phase_ledger_copy_exclusion >> simp[] >> metis_tac[]) >>
  `step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u` by simp[] >>
  drule_at (Pat `ricf_heterogeneous_source_ledger _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ricf_heterogeneous_source_ledger_located_activate >> simp[] >>
  disch_then (drule_at (Pat `ricf_located_event _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspec_then `next` mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qabbrev_tac `ledger' = if 0 < p.rpe_size then (p,[])::ledger else ledger` >>
  `p.rpe_dst = (a,da.inst_id) /\ p.rpe_src = (a,sa.inst_id)` by
    (drule ricf_history_origin_original_allocas >> simp[] >> strip_tac >> gvs[] >>
     drule_all ricf_located_event_source_descriptor >> strip_tac >> gvs[] >>
     metis_tac[ssa_alloca_output_unique, MEM]) >>
  `occurrence_allocas_ok B a s` by
    (drule occ_frame_reachable_annotation >> simp[occurrence_annotation_ok_def]) >>
  `occurrence_allocas_ok B p.rpe_owner p.rpe_before` by simp[] >>
  `FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
    FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size)` by
    (drule_all ricf_history_origin_endpoints >> simp[]) >>
  `p.rpe_db = db /\ p.rpe_sb = sb /\ p.rpe_size = w2n z` by gvs[] >>
  `ledger' = (p,[])::ledger` by simp[Abbr `ledger'`] >>
  `ricf_heterogeneous_support_origins vs C a fn U stk B (E UNION {p.rpe_dst})` by
    (irule ricf_heterogeneous_support_activate >> simp[] >> metis_tac[]) >>
  `step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u = G /\
   occurrence_sites_step a B (ricf_event_copy e (EL b fn.fn_blocks)) u = B /\
   occurrence_step a HP H (ricf_event_copy e (EL b fn.fn_blocks)) u = H` by
    simp[step_prov_def, set_prov_def, DRESTRICT_UNIV,
      occurrence_sites_step_def, occurrence_step_def] >>
  `eval_operand (Var dst) s = SOME (n2w db) /\
   eval_operand (Var sv) s = SOME (n2w sb) /\
   eval_operand (Lit z) s = SOME z` by
    gvs[eval_operands_def, AllCaseEqs()] >>
  `step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u rt =
   rt with t_mem := (rt.t_mem DIFF {i | db <= i /\ i < db+w2n z}) UNION
     {db+q | q < w2n z /\ sb+q IN rt.t_mem}` by
    (drule_all step_taint_mcopy >> simp[]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G
    (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u rt) u t` by
    (simp[] >> match_mp_tac (ricf_opaque_frame_source_mcopy_frontier |>
       Q.INST [`tn` |-> `rt`]) >> asm_simp_tac (srw_ss()) [ADD_COMM] >>
     conj_tac
     >- (irule SUBSET_TRANS >> qexists_tac `{i | db <= i /\ i < db+w2n z}` >>
         simp[SUBSET_DEF]) >>
     qpat_assum `!x y w k. (x,y,w) IN ricf_site_triples sites /\ k < w ==> _`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `ricf_opaque_live_stack_agree D (ricf_original_copy_ids C)
    (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u rt)
    maps stk targets u t` by
    (simp[] >> match_mp_tac (ricf_opaque_live_stack_source_mcopy_frontier |>
       Q.INST [`tn` |-> `rt`]) >> asm_simp_tac (srw_ss()) [ADD_COMM] >>
     qpat_assum `!j x y w k. j < LENGTH stk /\
       (x,y,w) IN ricf_site_triples (EL j maps) /\ k < w ==> _`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `ircf_cross (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u rt)
    (ricf_phase_ranges 0 ledger') u t` by
    (simp[UNION_COMM] >> match_mp_tac (ricf_cross_activate_copy |>
       Q.INST [`tn` |-> `rt`]) >> asm_simp_tac (srw_ss()) [ADD_COMM] >>
     qpat_assum `!gam x y w k.
       (gam = ricf_phase_ranges 0 ledger \/
         MEM gam (ricf_phase_stack_ranges stk ledger)) /\ (x,y,w) IN gam /\ k < w ==> _`
       (qspec_then `ricf_phase_ranges 0 ledger` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[ADD_COMM]) >>
  `ricf_cert_crosses (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u rt)
    (ricf_phase_stack_ranges stk ledger') stk u t` by
    (simp[] >>
     qpat_assum `ricf_cert_crosses rt _ stk s t`
       (strip_assume_tac o REWRITE_RULE [ricf_cert_crosses_def, EVERY_MEM]) >>
     asm_simp_tac (srw_ss()) [ricf_cert_crosses_def, EVERY_MEM] >>
     qx_gen_tac `gam` >> strip_tac >>
     match_mp_tac (ricf_cross_source_mcopy_frame |> Q.INST [`tn` |-> `rt`]) >>
     asm_simp_tac (srw_ss()) [ADD_COMM] >>
     qpat_assum `!gam x y w k.
       (gam = ricf_phase_ranges 0 ledger \/
         MEM gam (ricf_phase_stack_ranges stk ledger)) /\ (x,y,w) IN gam /\ k < w ==> _`
       (qspec_then `gam` mp_tac) >>
     qpat_assum `MEM gam (ricf_phase_stack_ranges stk ledger)` mp_tac >>
     qpat_assum `ricf_cert_crosses rt _ stk s t` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ricf_cert_crosses_def, EVERY_MEM] >>
     metis_tac[ADD_COMM]) >>
  `ricf_support_agree B (E UNION {p.rpe_dst})
    (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u rt) u t` by
    (simp[ADD_COMM] >> match_mp_tac
       (SRULE [ADD_COMM] (ricf_support_source_mcopy |> Q.INST [`tn` |-> `rt`])) >>
     simp[]) >>
  `~is_terminator (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode /\
    (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `ricf_heterogeneous_map_origins vs C stk PG
    (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
    (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn) fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx) U B sites` by
    (irule ricf_heterogeneous_map_origins_next >> metis_tac[]) >>
  `ricf_heterogeneous_saved_map_origins vs C stk PG
    (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
    (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn) fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx) U B maps` by
    (irule ricf_heterogeneous_saved_map_origins_next >> metis_tac[]) >>
  qexists_tac `p` >>
  simp[step_inst_def, step_inst_base_opcode_eqs] >>
  simp[ircf_dead_def, mcopy_def, write_memory_with_expansion_def,
    step_prov_def, set_prov_def, DRESTRICT_UNIV, occurrence_sites_step_def,
    occurrence_step_def] >>
  conj_tac >-
    (qpat_x_assum `ricf_heterogeneous_source_ledger _ _ _ _ _ _ fn next _ _ _ _ _ _ _ _`
       mp_tac >> simp[mcopy_def, write_memory_with_expansion_def,
         step_prov_def, set_prov_def, DRESTRICT_UNIV,
         occurrence_sites_step_def, occurrence_step_def]) >>
  conj_tac >-
    (qpat_assum `ricf_opaque_frame_agree fn _ _ _ _ _ _ u t`
       (mp_then Any (qspec_then `SUC s.vs_inst_idx` mp_tac) ricf_opaque_frame_inst_idx) >>
     qpat_assum `u = mcopy db sb (w2n z) s` mp_tac >>
     qpat_assum `s.vs_inst_idx = e.rfe_index` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ircf_dead_def, mcopy_def, write_memory_with_expansion_def]) >>
  conj_tac >-
    (qpat_x_assum `ricf_opaque_live_stack_agree _ _ _ _ _ _ u t` mp_tac >>
     qpat_assum `u = mcopy db sb (w2n z) s` mp_tac >>
     qpat_assum `s.vs_inst_idx = e.rfe_index` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ricf_opaque_live_stack_agree_def, ricf_opaque_frame_agree_def,
       ricf_opaque_view_def, merge_callee_state_def,
       mcopy_def, write_memory_with_expansion_def]) >>
  conj_tac >-
    (qpat_x_assum `ircf_cross _ _ u t` mp_tac >>
     qpat_assum `ledger' = (p,[])::ledger` mp_tac >>
     qpat_assum `u = mcopy db sb (w2n z) s` mp_tac >>
     qpat_assum `s.vs_inst_idx = e.rfe_index` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ircf_cross_def, mcopy_def, write_memory_with_expansion_def]) >>
  conj_tac >-
    (qpat_x_assum `ricf_cert_crosses _ _ _ u t` mp_tac >>
     qpat_assum `ledger' = (p,[])::ledger` mp_tac >>
     qpat_assum `u = mcopy db sb (w2n z) s` mp_tac >>
     qpat_assum `s.vs_inst_idx = e.rfe_index` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ricf_cert_crosses_def, ircf_cross_def,
       mcopy_def, write_memory_with_expansion_def]) >>
  conj_tac >-
    (qpat_x_assum `ricf_heterogeneous_support_origins _ _ _ _ _ _ _ (E UNION _)`
       mp_tac >>
     qpat_assum `p.rpe_dst = (a,da.inst_id)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `ricf_support_agree _ _ _ u t` mp_tac >>
     qpat_assum `p.rpe_dst = (a,da.inst_id)` mp_tac >>
     qpat_assum `u = mcopy db sb (w2n z) s` mp_tac >>
     qpat_assum `s.vs_inst_idx = e.rfe_index` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ricf_support_agree_def, mcopy_def, write_memory_with_expansion_def]) >>
  conj_tac >-
    (qpat_x_assum `ricf_heterogeneous_map_origins _ _ _ _ _ _ fn next _ _ _ _`
       mp_tac >>
     qpat_assum `u = mcopy db sb (w2n z) s` mp_tac >>
     qpat_assum `s.vs_inst_idx = e.rfe_index` mp_tac >>
     qpat_assum `step_prov PG G _ u = G` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[mcopy_def, write_memory_with_expansion_def]) >>
  qpat_x_assum `ricf_heterogeneous_saved_map_origins _ _ _ _ _ _ fn next _ _ _ _`
    mp_tac >>
  qpat_assum `u = mcopy db sb (w2n z) s` mp_tac >>
  qpat_assum `s.vs_inst_idx = e.rfe_index` mp_tac >>
  qpat_assum `step_prov PG G _ u = G` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED
