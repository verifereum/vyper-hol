Theory gasFocusConcretizeForwardWindow
Ancestors
  concretizePtrForwardingTransport concretizePtrPairedPrefix
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrOperationalOpcodes
  lowerDloadPtrForward lowerDloadPtrRawReachable stepWriteFootprintForward
  contextCodegenRel opcodeClass venomInstProofs1 venomExecSemantics
  venomState venomInst venomWf unitLabelMapIdentity list arithmetic

Theorem ptr_focus_paired_at_forwarding[local]:
  EVERY fn_inst_wf C.ctx_functions /\
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\ in_revert_forward a.po_fn a.po_state ==>
  in_revert_forward at.po_fn at.po_state
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_chrono_history_reachable >> strip_tac >>
  `MEM a.po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> simp[]) >>
  irule ptr_paired_cursor_forwarding >>
  qexistsl_tac [`a`, `lp`] >> simp[EVERY_MEM] >> rpt strip_tac >>
  `inst_wf inst` by
    (fs[EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  gvs[inst_wf_def]
QED

(* Interval geometry uses only the target step, independent of the source cut. *)
Theorem ptr_focus_forward_interval_step[local]:
  ptr_chrono_step Ct at zt /\ ALL_DISTINCT (fn_labels at.po_fn) /\
  lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\
  i <= at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j ==>
  zt.po_fn = at.po_fn /\ zt.po_state.vs_current_bb = at.po_state.vs_current_bb /\
  i < zt.po_state.vs_inst_idx /\ zt.po_state.vs_inst_idx <= j
Proof
  strip_tac >>
  `active_inst at.po_fn at.po_inst at.po_state` by
    (qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
     simp[Once ptr_chrono_step_cases] >> rpt strip_tac >> gvs[ptr_observe_def]) >>
  drule_all active_inst_block_lookup >> strip_tac >> gvs[] >>
  `i < j` by fs[revert_forward_pair_def] >>
  `at.po_inst.inst_opcode <> REVERT` by
    (qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
     simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
     gvs[ptr_observe_def, is_terminator_def] >> metis_tac[step_revert_no_normal]) >>
  `at.po_state.vs_inst_idx < j /\ ~is_terminator at.po_inst.inst_opcode /\
   at.po_inst.inst_opcode <> INVOKE` by
    (drule_all revert_forward_pair_interval_opcode >>
     rpt strip_tac >> gvs[is_terminator_def]) >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
  gvs[ptr_observe_def, step_inst_non_invoke]
  >- (drule_all step_inst_base_preserves_all >> simp[]) >>
  drule step_inst_base_intret_opcodes >> strip_tac >> gvs[is_terminator_def]
QED

Theorem ptr_focus_forward_window_successor:
  ptr_chrono_history vs Ct ht at /\ ptr_chrono_step Ct at zt /\
  EVERY fn_inst_wf C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) Ct.ctx_functions /\
  ((ptr_paired_prefix R lp positions lo vs C Ct
     h a ht at done tokens registry births PT TG saved entries H calls ws /\
    a.po_inst.inst_opcode <> NOP /\ in_revert_forward a.po_fn a.po_state) \/
   (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
     revert_forward_pair bb i j /\
     i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j)) ==>
  ?bb i j. lookup_block zt.po_state.vs_current_bb zt.po_fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\
    i < zt.po_state.vs_inst_idx /\ zt.po_state.vs_inst_idx <= j
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (drule ptr_chrono_history_reachable >>
     simp[ptr_observation_reachable_def] >> strip_tac >>
     drule ptr_frame_context_membership >> fs[EVERY_MEM] >> metis_tac[]) >>
  `?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
     revert_forward_pair bb i j /\
     i <= at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j` by
    (qpat_x_assum `_ \/ _` strip_assume_tac
     >- (drule_all ptr_focus_paired_at_forwarding >>
         simp[in_revert_forward_def, revert_forward_at_def] >>
         metis_tac[revert_forward_pair_def, LESS_IMP_LESS_OR_EQ, LESS_EQ_REFL]) >>
     qexistsl_tac [`bb`, `i`, `j`] >> simp[]) >>
  drule_all ptr_focus_forward_interval_step >> strip_tac >>
  qexistsl_tac [`bb`, `i`, `j`] >> simp[]
QED
