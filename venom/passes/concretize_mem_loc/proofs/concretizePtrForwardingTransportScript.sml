Theory concretizePtrForwardingTransport
Ancestors
  concretizePtrForwardingBoundary concretizePtrPairedFields
  concretizePtrLedgerAlignment contextCodegenRel venomInst
  concretizePtrPairedPrefix concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrDeletedGapHistory concretizePtrChronologicalHistory
  concretizePtrAllocationSize unitShapeDefs venomWf o1PassContract unitLabelMapIdentity
  list rich_list arithmetic

Theorem ptr_paired_cursor_forwarding:
  ptr_paired_cursor lp a at /\ a.po_inst.inst_opcode <> NOP /\
  EVERY (\bb. EVERY (\inst. inst.inst_opcode = NOP ==> inst.inst_outputs = [])
    bb.bb_instructions) a.po_fn.fn_blocks /\
  in_revert_forward a.po_fn a.po_state ==>
  in_revert_forward at.po_fn at.po_state
Proof
  rw[ptr_paired_cursor_def, in_revert_forward_def] >>
  `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
    (spose_not_then assume_tac >>
     `a.po_state.vs_inst_idx < EL at.po_state.vs_inst_idx indices` by decide_tac >>
     qpat_x_assum `!k. _` (qspec_then `a.po_state.vs_inst_idx` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `bb' = bb` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `EVERY (\inst. inst.inst_opcode = NOP ==> inst.inst_outputs = [])
     bb.bb_instructions` by (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_ledger_alignment_prefix_count >> strip_tac >>
  drule ptr_ledger_alignment_image >> strip_tac >>
  drule_all ptr_forwarding_at_rewrite >>
  disch_then (qspec_then `lp a.po_fn` mp_tac) >>
  simp[] >>
  simp[revert_forward_at_def, revert_forward_pair_def, get_instruction_def]
QED

Theorem ptr_paired_prefix_forwarding:
  o1_ctx_shape C /\ o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\ in_revert_forward a.po_fn a.po_state ==>
  in_revert_forward at.po_fn at.po_state
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  irule ptr_paired_cursor_forwarding >>
  qexistsl_tac [`a`, `lp`] >> simp[EVERY_MEM] >>
  rpt strip_tac >>
  `inst_wf inst` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def,
        fn_insts_MEM] >> metis_tac[]) >>
  gvs[inst_wf_def]
QED
