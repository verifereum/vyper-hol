(* Source histories with an independent transformation witness for each entry. *)
Theory readonlyInvokeCopyFwdHeterogeneousLedger
Ancestors
  readonlyInvokeCopyFwdHistoryPhaseAllocation
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdHistory
  readonlyInvokeCopyFwdPlan o1LowerDloadOccurrence finite_map list

Definition ricf_heterogeneous_source_ledger_def:
  ricf_heterogeneous_source_ledger vs C stk PG G tn fn inst s n a U B HP H ledger <=>
    occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
    EVERY (\entry. ?ctxP logP.
      ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B entry) ledger
End

Theorem ricf_heterogeneous_source_ledger_empty:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
  ricf_heterogeneous_source_ledger vs C stk PG G tn fn inst s n a U B HP H []
Proof
  simp[ricf_heterogeneous_source_ledger_def]
QED

Theorem ricf_heterogeneous_source_ledger_initial:
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>) s /\
  active_inst fn inst s ==>
  ricf_heterogeneous_source_ledger vs C [] [] FEMPTY entry_taint fn inst s
    1 0 [] FEMPTY [] FEMPTY []
Proof
  strip_tac >> irule ricf_heterogeneous_source_ledger_empty >>
  irule occ_frame_reachable_entry >> metis_tac[]
QED

Theorem ricf_heterogeneous_source_ledger_actual_next:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_heterogeneous_source_ledger vs C stk PG G tn fn inst s n a U B HP H ledger /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_heterogeneous_source_ledger vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx) n a U
    (occurrence_sites_step a B inst u) HP (occurrence_step a HP H inst u) ledger
Proof
  simp[ricf_heterogeneous_source_ledger_def, EVERY_MEM] >> rpt strip_tac
  >- (irule occ_frame_reachable_next >> metis_tac[]) >>
  `occurrence_allocas_ok B a s` by
    (drule occ_frame_reachable_annotation >> simp[occurrence_annotation_ok_def]) >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`ctxP`, `logP`] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (irule ricf_phase_entry_alloca >> metis_tac[]) >>
  irule ricf_phase_entry_next >> metis_tac[]
QED

Theorem ricf_heterogeneous_source_ledger_located_activate:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ricf_heterogeneous_source_ledger vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H ledger /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  active_inst fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\
  step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?p ledger'.
    p.rpe_event = e /\ p.rpe_block = EL b fn.fn_blocks /\ p.rpe_fn = fn /\
    p.rpe_before = s /\ p.rpe_after = u /\ p.rpe_owner = a /\
    ricf_history_origin vs C ctx0 log p stk PG G tn /\
    ledger' = (if 0 < p.rpe_size then (p,[])::ledger else ledger) /\
    ricf_heterogeneous_source_ledger vs C stk PG
      (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
      (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx) n a U
      (occurrence_sites_step a B (ricf_event_copy e (EL b fn.fn_blocks)) u)
      HP (occurrence_step a HP H (ricf_event_copy e (EL b fn.fn_blocks)) u) ledger' /\
    (!depth. ricf_phase_ranges depth ledger' =
      (if 0 < p.rpe_size /\ depth = 0
       then {(p.rpe_db,p.rpe_sb,p.rpe_size)} else {}) UNION
      ricf_phase_ranges depth ledger) /\
    ricf_phase_stack_ranges stk ledger' = ricf_phase_stack_ranges stk ledger
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H` by
    gvs[ricf_heterogeneous_source_ledger_def] >>
  `ricf_source_ledger vs C ctx0 log stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H []` by
    simp[ricf_source_ledger_def] >>
  drule_all ricf_source_ledger_activate >> strip_tac >>
  `(ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode = MCOPY` by
    (`ssa_form fn` by
       (drule occ_frame_reachable_annotation >>
        fs[EVERY_MEM, venomWfTheory.wf_ssa_def]) >>
     drule_all ricf_located_event_source_descriptor >> strip_tac >>
     drule ricf_located_event_validation >> strip_tac >>
     metis_tac[ricf_event_copy_shape]) >>
  `~is_terminator (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode /\
   (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode <> INVOKE` by
    simp[venomInstTheory.is_terminator_def] >>
  drule_all ricf_heterogeneous_source_ledger_actual_next >> strip_tac >>
  qexistsl_tac [`p`, `if 0 < p.rpe_size then (p,[])::ledger else ledger`] >>
  simp[ricf_phase_ranges_activation, ricf_phase_stack_ranges_activation] >>
  Cases_on `0 < p.rpe_size` >>
  gvs[ricf_heterogeneous_source_ledger_def, ricf_source_ledger_def] >>
  metis_tac[]
QED
