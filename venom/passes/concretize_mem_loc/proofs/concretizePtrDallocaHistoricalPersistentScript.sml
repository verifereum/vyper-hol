Theory concretizePtrDallocaHistoricalPersistent
Ancestors
  concretizePtrDallocaPersistentChannels concretizePtrDallocaPersistentSteps
  concretizePtrDallocaWriterGeometry concretizePtrHistoricalWriteExclusion
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrTaggedSupport
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrSourceOwnership concretizePtrChronologicalHistory
  concretizePtrRequestHistory concretizePtrOpaqueRetpc
  concretizeMemLocDefs passSharedDefs o1PassContract unitShapeDefs
  ptrDiscipline venomWf venomInst venomState list finite_map pred_set

Theorem ptr_dalloca_historical_sample:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  q < LENGTH done /\ a = EL (EL q done) h /\ t = EL q ht ==>
  ptr_snapshot_ownership vs C (TAKE (SUC (EL q done)) h) a (EL (EL q done) H) /\
  ptr_paired_sample positions a t (EL (EL q done) H) /\
  ptr_observation_reachable vs C a
Proof
  strip_tac >> drule ptr_paired_prefix_samples >> strip_tac >>
  `q < LENGTH ht /\ EL q done < LENGTH h` by
    fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  rpt conj_tac
  >- (drule ptr_structural_transcript_ownership >>
      disch_then (qspec_then `EL q done` mp_tac) >> simp[])
  >- (qpat_x_assum `ptr_paired_samples _ _ _ _ _` mp_tac >>
      pure_rewrite_tac[ptr_paired_samples_def, ptr_sample_list_def] >>
      strip_tac >> first_x_assum (qspec_then `q` mp_tac) >>
      simp[EL_APPEND_EQN]) >>
  drule ptr_structural_trace_source >>
  disch_then (mp_tac o MATCH_MP ptr_chrono_history_reachable) >>
  simp[EVERY_MEM] >> strip_tac >> first_x_assum irule >>
  simp[MEM_EL] >> qexists `EL q done` >> simp[]
QED

(* The recorded snapshot supplies ownership at the departure, independently
   of the final activation stack and allocation ledger. *)
Theorem ptr_dalloca_historical_persistent_context:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\
  q < LENGTH done /\ a = EL (EL q done) h /\ t = EL q ht ==>
  ?P bj TGj.
    MEM a.po_fn C.ctx_functions /\
    fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn /\
    MEM a.po_inst (fn_insts a.po_fn) /\ inst_wf a.po_inst /\
    taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
    (!v tag. FLOOKUP TGj v = SOME tag ==> v IN fn_pv P a.po_fn) /\
    ptr_mixed_vars (bj:(num # num, num # num) fmap) positions
      (TGj:(string, num # num) fmap) a.po_taint a.po_fn t.po_fn
      a.po_state t.po_state /\
    ptr_history_content a.po_taint a.po_state t.po_state /\
    a.po_state.vs_labels = t.po_state.vs_labels
Proof
  strip_tac >> drule_all ptr_dalloca_historical_sample >> strip_tac >>
  qabbrev_tac `snapshot = EL (EL q done) H` >> PairCases_on `snapshot` >>
  fs[ptr_snapshot_ownership_def, ptr_paired_sample_def] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_dalloca_writer_instruction_facts >> strip_tac >>
  `MEM a.po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >>
     drule concretizePtrOperationalOpcodesTheory.ptr_frame_context_membership >> simp[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def,
        fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >> metis_tac[]) >>
  `inst_wf a.po_inst` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_observation_reachable_def, ptr_discipline_def] >> metis_tac[]) >>
  `!v tag. FLOOKUP snapshot4 v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> irule ptr_source_tagged_var_support >>
     rpt (goal_assum (drule_at Any))) >>
  qexistsl_tac [`P`,`snapshot2`,`snapshot4`] >> simp[] >>
  metis_tac[ptr_history_content_labels]
QED

Theorem ptr_dalloca_historical_persistent_next:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\
  q < LENGTH done /\ a = EL (EL q done) h /\ t = EL q ht /\
  step_inst fuel C a.po_inst a.po_state = OK post /\
  step_inst fuelT C' t.po_inst t.po_state = OK postT /\
  t.po_taint.t_stor SUBSET a.po_taint.t_stor /\
  t.po_taint.t_trans SUBSET a.po_taint.t_trans /\
  t.po_taint.t_imm SUBSET a.po_taint.t_imm /\
  (!op. MEM op a.po_inst.inst_operands ==>
    op_taint t.po_taint op SUBSET op_taint a.po_taint op) ==>
  (step_taint t.po_inst t.po_state postT t.po_taint).t_stor SUBSET
    (step_taint a.po_inst a.po_state post a.po_taint).t_stor /\
  (step_taint t.po_inst t.po_state postT t.po_taint).t_trans SUBSET
    (step_taint a.po_inst a.po_state post a.po_taint).t_trans /\
  (step_taint t.po_inst t.po_state postT t.po_taint).t_imm SUBSET
    (step_taint a.po_inst a.po_state post a.po_taint).t_imm
Proof
  strip_tac >> drule_all ptr_dalloca_historical_persistent_context >> strip_tac >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `q < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  drule_all (Q.INST [`j` |-> `q`] ptr_paired_prefix_alignment) >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `a.po_inst.inst_id = t.po_inst.inst_id` by
    (drule ptr_trace_departed_inst_ids >>
     disch_then (qspec_then `q` mp_tac) >> simp[]) >>
  `fn_inst_ids_distinct a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
        EVERY_MEM, wf_function_def] >> metis_tac[]) >>
  `t.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst` by
    (irule ptr_departed_cursor_instruction >> gvs[EL_APPEND_EQN]) >>
  `!key data. MEM a.po_inst.inst_opcode [SSTORE;TSTORE;ISTORE] /\
    a.po_inst.inst_operands = [key;data] ==>
    eval_operand key t.po_state = eval_operand key a.po_state` by
    (rpt strip_tac >> drule_all ptr_dalloca_store_selector_equal >> simp[]) >>
  Cases_on `a.po_inst.inst_opcode = ALLOCA`
  >- (`t.po_inst = a.po_inst \/ t.po_inst.inst_opcode = ASSIGN \/
       t.po_inst.inst_opcode = NOP` by
        (qpat_x_assum `t.po_inst = concretize_inst_with_positions _ _` mp_tac >>
         qpat_x_assum `a.po_inst.inst_opcode = ALLOCA` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         gvs[concretize_inst_with_positions_def, AllCaseEqs(),
             mk_assign_inst_def, mk_nop_inst_def] >>
         qpat_x_assum `_ = t.po_inst` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
      gvs[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def]) >>
  `t.po_inst = a.po_inst` by
    (qpat_x_assum `t.po_inst = concretize_inst_with_positions _ _` mp_tac >>
     simp[concretize_inst_with_positions_def]) >>
  `step_inst fuelT C' a.po_inst t.po_state = OK postT` by metis_tac[] >>
  `a.po_inst.inst_opcode = CALL ==>
    ptr_call_adopted a.po_state post = ptr_call_adopted t.po_state postT` by
    (strip_tac >> drule_all ptr_dalloca_call_adoption >> simp[]) >>
  irule ptr_dalloca_persistent_next >> simp[] >>
  gvs[concretizePtrRequestCompletionProbeTheory.ptr_call_adopted_def]
QED
