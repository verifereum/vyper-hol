(* Joint actual copy execution and heterogeneous phase-ledger insertion. *)
Theory readonlyInvokeCopyFwdOperationalCopyLedger
Ancestors
  readonlyInvokeCopyFwdOperationalPositiveCopy
  readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdOperationalMapOrigins
  readonlyInvokeCopyFwdHistoryVisitAccess
  readonlyInvokeCopyFwdHistoryAvailability
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdTraceOrigin
  o1LowerDloadOccurrence mem2varProofs
  internalReturnCopyFwdSim venomWfProps finite_map list pred_set words

Theorem ricf_operational_positive_copy_ledger:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\ ssa_form fn /\ fn_inst_wf fn /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;Lit z] /\
  0 < w2n z /\ occurrence_natural_geometry lo a U B stk s /\
  s.vs_alloca_next <= dimword (:256) /\
  ricf_cert_core D (ricf_original_copy_ids C) stk PG G tn fn
    sites maps targets G0 tn0 (ricf_phase_ranges 0 ledger)
    (ricf_phase_stack_ranges stk ledger) s t /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  ricf_support_agree B E tn0 s t /\
  ricf_map_origins vs C ctx0 log stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s U B sites /\
  ricf_saved_map_origins vs C ctx0 log stk U B maps /\
  EVERY (\entry. ?ctxP logP.
    ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B entry) ledger /\
  active_inst fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\ wf_function fn /\
  access_ok lo G fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\
  ~in_revert_forward fn s /\
  nop.inst_opcode = NOP /\ nop.inst_operands = [] /\ nop.inst_outputs = [] /\
  (!u. step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u ==>
    active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  ?did sid db sb un u p ledger'.
    FLOOKUP H dst = SOME (a,did) /\ FLOOKUP H sv = SOME (a,sid) /\
    did IN ricf_original_copy_ids C /\ did <> sid /\
    FLOOKUP B (a,did) = SOME (db,w2n z) /\
    FLOOKUP B (a,sid) = SOME (sb,w2n z) /\
    un = tn0 with t_mem :=
      (tn0.t_mem DIFF {i | db <= i /\ i < db+w2n z}) UNION
      {db+q | q < w2n z /\ sb+q IN tn0.t_mem} /\
    u = mcopy db sb (w2n z) s /\
    step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u /\
    step_inst fuel Ct nop t = OK t /\
    p.rpe_event = e /\ p.rpe_block = EL b fn.fn_blocks /\ p.rpe_fn = fn /\
    p.rpe_before = s /\ p.rpe_after = u /\ p.rpe_owner = a /\
    ricf_history_origin vs C ctx0 log p stk PG G tn /\
    p.rpe_db = db /\ p.rpe_sb = sb /\ p.rpe_size = w2n z /\
    ledger' = (p,[])::ledger /\
    ricf_heterogeneous_source_ledger vs C stk PG
      (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
      (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx) n a U
      (occurrence_sites_step a B (ricf_event_copy e (EL b fn.fn_blocks)) u)
      HP (occurrence_step a HP H (ricf_event_copy e (EL b fn.fn_blocks)) u) ledger' /\
    ricf_cert_core D (ricf_original_copy_ids C) stk PG
      (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
      (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn)
      fn sites maps targets G0 un (ricf_phase_ranges 0 ledger')
      (ricf_phase_stack_ranges stk ledger')
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    ricf_support_agree B (E UNION {(a,did)}) un u t /\
    ricf_global_support_origins vs C ctx0 a fn U stk B (E UNION {(a,did)})
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST
    [`cur` |-> `ricf_phase_ranges 0 ledger`,
     `curs` |-> `ricf_phase_stack_ranges stk ledger`]
    ricf_operational_positive_copy)) >>
  disch_then (qspecl_then [`fuel`,`Ct`] strip_assume_tac) >>
  qabbrev_tac `u = mcopy db sb (w2n z) s` >>
  qmatch_asmsub_abbrev_tac `ricf_support_agree B (E UNION {(a,did)}) un u t` >>
  `ricf_heterogeneous_source_ledger vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H ledger` by
    simp[ricf_heterogeneous_source_ledger_def] >>
  `active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx)` by metis_tac[] >>
  drule_all ricf_heterogeneous_source_ledger_located_activate >> strip_tac >>
  `p.rpe_db = db /\ p.rpe_sb = sb /\ p.rpe_size = w2n z` by
    (drule_all ricf_located_event_operands_available >> strip_tac >> gvs[] >>
     drule_all ricf_history_origin_original_allocas >> strip_tac >> gvs[] >>
     drule_all ricf_located_event_source_descriptor >> strip_tac >> gvs[] >>
     `occurrence_allocas_ok B p.rpe_owner p.rpe_before` by
       (drule occ_frame_reachable_annotation >>
        simp[occurrence_annotation_ok_def]) >>
     drule_all ricf_history_origin_endpoints >> strip_tac >>
     `da = da' /\ sa = sa'` by metis_tac[ssa_alloca_output_unique, MEM] >>
     gvs[]) >>
  qexistsl_tac [`did`,`sid`,`db`,`sb`,`un`,`u`,`p`,`ledger'`] >>
  gvs[UNION_COMM]
QED

Theorem ricf_operational_copy_ledger_initial:
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) s /\
  active_inst fn inst s /\ s.vs_prev_bb = NONE /\
  taint_agree D (ircf_dead (ricf_original_copy_ids C) s []) entry_taint s s ==>
  ricf_heterogeneous_source_ledger vs C [] [] FEMPTY entry_taint fn inst s
    1 0 [] FEMPTY [] FEMPTY [] /\
  ricf_cert_core D (ricf_original_copy_ids C) [] [] FEMPTY entry_taint fn
    FEMPTY [] [] FEMPTY entry_taint (ricf_phase_ranges 0 [])
    (ricf_phase_stack_ranges [] []) s s
Proof
  strip_tac >> conj_tac
  >- (irule ricf_heterogeneous_source_ledger_initial >> metis_tac[]) >>
  simp[ricf_phase_stack_ranges_def, ricf_cert_core_def, ricf_cert_crosses_def,
    ricf_live_boundary_core_def, ricf_frame_agree_completed_identity,
    ricf_live_stack_agree_def, ircf_cross_def]
QED
