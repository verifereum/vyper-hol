Theory gasFocusConcretizeForwardWindow
Ancestors concretizePtrHistoryCoverage[qualified]
  concretizePtrForwardingTransport concretizePtrPairedPrefix
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrOperationalOpcodes
  lowerDloadPtrForward lowerDloadPtrRawReachable stepWriteFootprintForward
  contextCodegenRel opcodeClass venomInstProofs1 venomExecSemantics
  venomState venomInst venomWf unitLabelMapIdentity list arithmetic
  concretizePtrRevertHistory[qualified,ignore_grammar]

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
     >- (drule_all concretizePtrHistoryCoverageTheory.ptr_paired_history_forwarding_transport >>
         simp[in_revert_forward_def, revert_forward_at_def] >>
         metis_tac[revert_forward_pair_def, LESS_IMP_LESS_OR_EQ, LESS_EQ_REFL]) >>
     qexistsl_tac [`bb`, `i`, `j`] >> simp[]) >>
  drule_all concretizePtrRevertHistoryTheory.ptr_revert_interval_step >> strip_tac >>
  qexistsl_tac [`bb`, `i`, `j`] >> simp[]
QED
