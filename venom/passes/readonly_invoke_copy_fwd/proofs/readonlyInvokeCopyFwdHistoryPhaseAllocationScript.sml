(* ALLOCA transport for the source-only phase ledger.  Existing occurrence
   keys persist in both the fresh and cached allocation branches. *)
Theory readonlyInvokeCopyFwdHistoryPhaseAllocation
Ancestors
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdHistoryOrigin
  o1LowerDloadOccurrence finite_map list

Theorem ricf_phase_entry_alloca:
  ricf_phase_entry vs C ctx0 log stk PG G tn fn s a U B entry /\
  occurrence_allocas_ok B a s /\
  active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  step_inst fuel C inst s = OK u ==>
  ricf_phase_entry vs C ctx0 log stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn (u with vs_inst_idx := SUC s.vs_inst_idx)
    a U (occurrence_sites_step a B inst u) entry
Proof
  Cases_on `entry` >> simp[ricf_phase_entry_def] >> rpt strip_tac
  >- (irule ricf_history_cursor_next >>
      simp[venomInstTheory.is_terminator_def] >> metis_tac[])
  >- (irule occurrence_sites_step_preserves >> metis_tac[])
  >- (irule occurrence_sites_step_preserves >> metis_tac[]) >>
  simp[]
QED

Theorem ricf_source_ledger_alloca:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_source_ledger vs C ctx0 log stk PG G tn fn inst s n a U B HP H ledger /\
  active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_source_ledger vs C ctx0 log stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx) n a U
    (occurrence_sites_step a B inst u) HP (occurrence_step a HP H inst u) ledger
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ricf_source_ledger_occurrence] >>
  `occurrence_allocas_ok B a s` by
    (drule occ_frame_reachable_annotation >>
     simp[occurrence_annotation_ok_def]) >>
  simp[ricf_source_ledger_def, EVERY_MEM] >> conj_tac
  >- (irule occ_frame_reachable_next >>
      simp[venomInstTheory.is_terminator_def] >> metis_tac[]) >>
  rpt strip_tac >> irule ricf_phase_entry_alloca >>
  gvs[ricf_source_ledger_def, EVERY_MEM] >> metis_tac[]
QED
