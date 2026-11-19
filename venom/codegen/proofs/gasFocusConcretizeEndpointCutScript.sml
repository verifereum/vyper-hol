Theory gasFocusConcretizeEndpointCut
Ancestors
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizePtrSourceOwnership
  concretizePtrRequestHistory concretizePtrTaintContent
  concretizePtrPairedFields concretizePtrSharedFields concretizePtrOpaqueRetpc
  concretizeLayoutCutSafe o1SafeUpto

(* The paired endpoint retains readings even though request histories differ. *)
Theorem ptr_paired_endpoint_readings:
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws ==>
  a.po_state.vs_gas_readings = at.po_state.vs_gas_readings
Proof
  strip_tac >> drule ptr_paired_prefix_endpoint >> strip_tac >>
  fs[ptr_paired_sample_def] >> drule ptr_history_content_control >>
  simp[ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def]
QED

(* Localize bounded source safety at the paired target's current cut. *)
Theorem ptr_paired_endpoint_cut_safety:
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_discipline_upto lo n C vs /\ gas_cut n vs at.po_state ==>
  frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state /\
  gas_cut n vs a.po_state /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  allocas_from lo a.po_state /\
  (ctx_has_dalloca C ==> allocas_below_fmp a.po_state)
Proof
  strip_tac >>
  drule ptr_paired_endpoint_readings >> strip_tac >>
  `gas_cut n vs a.po_state` by fs[gas_cut_def] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule ptr_gap_ownership_history >> strip_tac >>
  drule ptr_chrono_history_reachable >>
  simp[ptr_observation_reachable_def] >> strip_tac >>
  drule_all ptr_discipline_upto_at >> simp[]
QED
