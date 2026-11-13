Theory readonlyInvokeCopyFwdOperationalGuards
Ancestors
  readonlyInvokeCopyFwdHistoryAvailability readonlyInvokeCopyFwdOperationalPositiveCopy
  readonlyInvokeCopyFwdOperationalCopyLedger readonlyInvokeCopyFwdOperationalZeroCopy
  readonlyInvokeCopyFwdOperationalRevert readonlyInvokeCopyFwdCopyAnnotations
  readonlyInvokeCopyFwdOperationalMapOrigins readonlyInvokeCopyFwdGlobalSupport
  readonlyInvokeCopyFwdHistoryInheritedLifecycle readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdHistoryPhase
  codegenRel ptrDiscipline
  readonlyInvokeCopyFwdRel taintAgree o1LowerDloadShared o1LowerDloadOccurrence
  internalReturnCopyFwdSim venomInst venomState finite_map list pred_set words

(* Source annotation taint and relational byte taint are independent indices. *)
Definition ricf_operational_invariant_def:
  ricf_operational_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets G0 tn0 <=>
  ricf_heterogeneous_source_ledger vs C stk PG G tn fn inst s n a U B HP H ledger /\
  ricf_cert_core D (ricf_original_copy_ids C) stk PG G tn fn sites maps targets
    G0 tn0 (ricf_phase_ranges 0 ledger) (ricf_phase_stack_ranges stk ledger) s t /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  ricf_support_agree B E tn0 s t /\
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites /\
  ricf_saved_map_origins vs C ctx0 log stk U B maps
End

(* Identity initialization is stronger than required: no cleanliness premise
   is needed for reflexive agreement, even for arbitrary entry taint. *)
Theorem ricf_operational_initial:
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s /\
  active_inst fn inst s /\ s.vs_prev_bb = NONE ==>
  ricf_operational_invariant vs C ctx0 log D [] [] FEMPTY entry_taint fn inst s s
    1 0 [] FEMPTY [] FEMPTY [] {} FEMPTY [] [] FEMPTY entry_taint
Proof
  strip_tac >>
  `taint_agree D (ircf_dead (ricf_original_copy_ids C) s []) entry_taint s s` by
    simp[taint_agree_def, ld_shared_agree_refl, word_agree_except_def,
         venom_state_component_equality] >>
  drule_all ricf_operational_copy_ledger_initial >> strip_tac >>
  gvs[ricf_operational_invariant_def, ricf_global_support_empty,
    ricf_support_agree_def, ricf_map_origins_empty,
    ricf_phase_stack_ranges_def]
QED

Theorem ricf_translation_origin_next:
  ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U B key tr /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_translation_origin vs C ctx0 log stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U B key tr
Proof
  rw[ricf_translation_origin_def] >>
  qexistsl_tac [`p`,`pre`,`anchor`,`tail`,`atn`] >> simp[] >>
  irule ricf_history_inherited_next >> metis_tac[]
QED

Theorem ricf_map_origins_next:
  ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_map_origins vs C ctx0 log stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U B sites
Proof
  rw[ricf_map_origins_def] >> irule ricf_translation_origin_next >> metis_tac[]
QED

Theorem ricf_operational_positive_transition:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ssa_form fn /\ fn_inst_wf fn /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;Lit z] /\
  0 < w2n z /\ occurrence_natural_geometry lo a U B stk s /\
  s.vs_alloca_next <= dimword (:256) /\
  ricf_operational_invariant vs C ctx0 log D stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s t
    n a U B HP H ledger E sites maps targets G0 tn0 /\
  active_inst fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\ wf_function fn /\
  access_ok lo G fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\
  ~in_revert_forward fn s /\
  nop.inst_opcode = NOP /\ nop.inst_operands = [] /\ nop.inst_outputs = [] /\
  (!u. step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u ==>
    active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  ?did u un p.
    FLOOKUP H dst = SOME (a,did) /\
    p.rpe_event = e /\ p.rpe_before = s /\ p.rpe_after = u /\
    step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u /\
    step_inst fuel Ct nop t = OK t /\
    ricf_operational_invariant vs C ctx0 log D stk PG
      (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
      (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (t with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B (ricf_event_copy e (EL b fn.fn_blocks)) u)
      HP (occurrence_step a HP H (ricf_event_copy e (EL b fn.fn_blocks)) u)
      ((p,[])::ledger) (E UNION {(a,did)}) sites maps targets G0 un
Proof
  pure_rewrite_tac[ricf_operational_invariant_def] >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
   EVERY (\entry. ?ctxP logP.
     ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B entry) ledger` by
    fs[ricf_heterogeneous_source_ledger_def] >>
  drule_all ricf_operational_positive_copy_ledger >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  `active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx)` by metis_tac[] >>
  `~is_terminator (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode /\
   (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode <> INVOKE /\
   occurrence_sites_step a B (ricf_event_copy e (EL b fn.fn_blocks)) u = B` by
    (drule_all ricf_located_event_operands_available >> strip_tac >>
     simp[is_terminator_def, occurrence_sites_step_def]) >>
  `ricf_map_origins vs C ctx0 log stk PG
    (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
    (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn) fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx) U B sites` by
    (irule ricf_map_origins_next >> metis_tac[]) >>
  qexistsl_tac [`did`,`u`,`un`,`p`] >>
  gvs[ricf_support_agree_def] >> metis_tac[]
QED

Theorem ricf_operational_zero_transition:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;Lit 0w] /\
  ricf_operational_invariant vs C ctx0 log D stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s t
    n a U B HP H ledger E sites maps targets G0 tn0 /\
  active_inst fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\
  nop.inst_opcode = NOP /\ nop.inst_operands = [] /\ nop.inst_outputs = [] /\
  (!u. step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u ==>
    active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  ?u.
    step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u /\
    step_inst fuel Ct nop t = OK t /\
    ricf_operational_invariant vs C ctx0 log D stk PG
      (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
      (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (t with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B (ricf_event_copy e (EL b fn.fn_blocks)) u)
      HP (occurrence_step a HP H (ricf_event_copy e (EL b fn.fn_blocks)) u)
      ledger E sites maps targets G0 tn0
Proof
  pure_rewrite_tac[ricf_operational_invariant_def] >> strip_tac >>
  `tn.t_mem = tn0.t_mem /\ s.vs_inst_idx = t.vs_inst_idx` by
    (fs[ricf_cert_core_def, ricf_live_boundary_core_def, entry_taint_vars_def,
        ricf_frame_agree_def, taint_agree_def, venom_state_component_equality] >>
     Cases_on `s.vs_prev_bb = NONE` >> gvs[]) >>
  `ricf_support_agree B E tn s t` by fs[ricf_support_agree_def] >>
  drule_all ricf_operational_zero_copy >>
  disch_then (qspecl_then [`fuel`,`Ct`] strip_assume_tac) >>
  `active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx)` by metis_tac[] >>
  `occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H` by
    fs[ricf_heterogeneous_source_ledger_def] >>
  `~is_terminator (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode /\
   (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode <> INVOKE /\
   occurrence_sites_step a B (ricf_event_copy e (EL b fn.fn_blocks)) u = B` by
    (drule_all ricf_located_event_operands_available >> strip_tac >>
     simp[is_terminator_def, occurrence_sites_step_def]) >>
  `ricf_map_origins vs C ctx0 log stk PG
    (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
    (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn) fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx) U B sites` by
    (irule ricf_map_origins_next >> metis_tac[]) >>
  ` (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn).t_mem = tn0.t_mem` by
    (qpat_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ (u with vs_inst_idx := _) _`
       mp_tac >>
     pure_rewrite_tac[ricf_cert_core_def, ricf_live_boundary_core_def] >>
     strip_tac >>
     qpat_x_assum `step_taint _ _ _ _ = _`
       (mp_tac o Q.AP_TERM `\x. x.t_mem`) >>
     Cases_on `u.vs_prev_bb = NONE` >> simp[entry_taint_vars_def] >>
     Cases_on `lookup_block u.vs_current_bb fn.fn_blocks` >> simp[]) >>
  qexists_tac `u` >> gvs[ricf_support_agree_def] >> metis_tac[]
QED

Theorem ricf_operational_copy_transition:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ssa_form fn /\ fn_inst_wf fn /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;Lit z] /\
  occurrence_natural_geometry lo a U B stk s /\
  s.vs_alloca_next <= dimword (:256) /\
  ricf_operational_invariant vs C ctx0 log D stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s t
    n a U B HP H ledger E sites maps targets G0 tn0 /\
  active_inst fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\ wf_function fn /\
  access_ok lo G fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\
  ~in_revert_forward fn s /\
  nop.inst_opcode = NOP /\ nop.inst_operands = [] /\ nop.inst_outputs = [] /\
  (!u. step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u ==>
    active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  ?u un ledger' E'.
    step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u /\
    step_inst fuel Ct nop t = OK t /\
    (if z = 0w then ledger' = ledger /\ E' = E /\ un = tn0
     else ?did p. FLOOKUP H dst = SOME (a,did) /\
       p.rpe_event = e /\ p.rpe_before = s /\ p.rpe_after = u /\
       ledger' = (p,[])::ledger /\ E' = E UNION {(a,did)}) /\
    ricf_operational_invariant vs C ctx0 log D stk PG
      (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
      (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (t with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B (ricf_event_copy e (EL b fn.fn_blocks)) u)
      HP (occurrence_step a HP H (ricf_event_copy e (EL b fn.fn_blocks)) u)
      ledger' E' sites maps targets G0 un
Proof
  strip_tac >> Cases_on `z = 0w`
  >- (qpat_x_assum `z = 0w` SUBST_ALL_TAC >>
      drule_all ricf_operational_zero_transition >>
      disch_then (qspec_then `Ct` strip_assume_tac) >>
      qexistsl_tac [`u`,`tn0`,`ledger`,`E`] >> simp[]) >>
  `0 < w2n z` by (Cases_on `z` >> gvs[]) >>
  drule_all ricf_operational_positive_transition >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  qexistsl_tac [`u`,`un`,`(p,[])::ledger`,`E UNION {(a,did)}`] >>
  simp[] >> metis_tac[]
QED
