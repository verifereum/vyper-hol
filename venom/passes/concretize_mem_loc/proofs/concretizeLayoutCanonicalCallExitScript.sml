Theory concretizeLayoutCanonicalCallExit
Ancestors concretizeLayoutCanonicalDriver concretizeLayoutCallRunEntry
  concretizeLayoutPairedEntry concretizeLayoutAlignedControl
  concretizeLayoutPhaseCorridor concretizeLayoutPhaseOrigin
  frameRankedTerminalCorridor concretizeStepStructure
  frameSelectedSimulation venomInst list arithmetic

Theorem layout_canonical_invoke_witness:
  layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t /\
  i.inst_opcode = INVOKE ==>
  j = i /\ ?a. layout_driver_indexed es ass a /\
    ~a.lop_pending /\ a.lop_config = q /\ a.lop_cursor = n /\
    layout_aligned_entry D lo vs0 C C' q0 es qs qend a s t
Proof
  simp[layout_canonical_ES_def, layout_canonical_step_witness_def] >>
  strip_tac >> Cases_on `a`
  >- (gvs[layout_canonical_block_witness_def, layout_paired_ordinary_def,
          concretize_positions_unchanged] >> metis_tac[]) >>
  gvs[layout_canonical_block_witness_def, layout_corridor_entry_def,
      ranked_terminal_entry_def, layout_phase_normalize_def] >>
  Cases_on `y.ltp_remaining`
  >- gvs[ranked_terminal_corridor_def] >>
  fs[ranked_terminal_corridor_def] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]
QED

val _ = export_theory();
