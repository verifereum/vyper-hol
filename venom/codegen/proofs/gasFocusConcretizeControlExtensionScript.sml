Theory gasFocusConcretizeControlExtension
Ancestors
  gasFocusConcretizeInvokeSuccessor gasFocusConcretizeJumpScalar
  concretizePtrPairedJump concretizePtrPairedJumpEntry
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrChronologicalHistory
  concretizePtrDeletedGapHistory concretizePtrOpaqueRetpc
  concretizePtrRequestHistory concretizePtrValueTransport
  concretizePtrOperationalOpcodes concretizeStepStructure
  contextCodegenRel ptrDiscipline unitShapeDefs venomWf venomInst
  pointerConfinedDefs o1PassContract unitLabelMapIdentity
  venomExecSemantics finite_map list words

Theorem ptr_focus_invoke_extension:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  (?P. EVERY (fn_ptr_ok P) C.ctx_functions) /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  allocas_from lo a.po_state /\
  (ctx_has_dalloca C ==> allocas_below_fmp a.po_state) /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  EVERY (\f. first_block_no_phi f /\ fn_inst_wf f /\ opaque_use_ok f /\
    EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  a.po_inst.inst_opcode = INVOKE /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_focus_invoke_successor >> strip_tac >>
  qexistsl_tac [`[b] ++ delta`, `ptr_gap_scan bb n b`,
    `LENGTH h :: tokens`, `registry |+ (LENGTH h,f)`, `B`,
    `MAP (op_prov TG) ops`, `FEMPTY`, `(PT,TG)::saved`,
    `entries |+ (LENGTH h,LENGTH ht)`,
    `[(LENGTH h :: tokens,registry |+ (LENGTH h,f),B,
       MAP (op_prov TG) ops,FEMPTY,(PT,TG)::saved,
       entries |+ (LENGTH h,LENGTH ht))] ++ snapshots`,
    `(LENGTH h - 1,LENGTH ht - 1)::calls`, `ws`] >>
  gvs[APPEND_ASSOC]
QED

Theorem ptr_focus_jump_extension:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  (?P. EVERY (fn_ptr_ok P) C.ctx_functions) /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  allocas_from lo a.po_state /\
  (ctx_has_dalloca C ==> allocas_below_fmp a.po_state) /\
  o1_ctx_shape C /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [JMP; JNZ; DJMP] ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst
Proof
  strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `MEM a.po_fn C.ctx_functions /\ active_inst a.po_fn a.po_inst a.po_state` by
    (drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_reachable >>
     simp[ptr_observation_reachable_def] >> strip_tac >>
     conj_tac >- (drule ptr_frame_context_membership >> simp[]) >>
     qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >> gvs[]) >>
  `MEM at.po_fn C'.ctx_functions` by
    (drule ptr_structural_trace_target >> strip_tac >>
     drule ptr_chrono_history_reachable >>
     simp[ptr_observation_reachable_def] >> strip_tac >>
     drule ptr_frame_context_membership >> simp[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\ opaque_use_ok a.po_fn /\
   EVERY bb_well_formed a.po_fn.fn_blocks /\
   ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
   (!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
     IS_SOME (FLOOKUP (lp a.po_fn) (Allocation i.inst_id)))` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `at.po_inst = a.po_inst` by
    (fs[MEM] >> gvs[concretize_positions_unchanged]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def, MEM]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()]) >>
  `zt = ptr_observe at.po_stack at.po_params
    (entry_prov at.po_fn s' at.po_prov)
    (entry_taint_vars at.po_fn s' at.po_taint) at.po_fn zt.po_inst zt.po_state` by
    simp[ptr_observation_component_equality, ptr_observe_def] >>
  `active_inst at.po_fn at.po_inst at.po_state /\
   step_inst fuel C' at.po_inst at.po_state = OK s' /\
   at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
   is_terminator at.po_inst.inst_opcode` by simp[is_terminator_def]
  >>~- ([`a.po_inst.inst_opcode = JMP`],
    drule_all ptr_paired_jump_prefix_normalize >> strip_tac >> suspend "pack")
  >>~- ([`a.po_inst.inst_opcode = JNZ`],
    `?cond yes no. a.po_inst.inst_operands = [cond; Label yes; Label no]` by
      (`MEM a.po_inst (fn_insts a.po_fn)` by
         (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
       `inst_wf a.po_inst` by (fs[EVERY_MEM] >> metis_tac[]) >>
       gvs[inst_wf_def] >> metis_tac[]) >>
    `MEM a.po_inst.inst_opcode [JNZ; DJMP] /\ MEM cond a.po_inst.inst_operands` by simp[] >>
    drule_all ptr_focus_jump_scalar >> strip_tac >>
    drule_all ptr_paired_jnz_prefix_normalize >> strip_tac >> suspend "pack")
  >> suspend "djmp"
QED

Resume ptr_focus_jump_extension[pack]:
  markerLib.RESUME_TAC >>
  qexistsl_tac [`[b] ++ delta`, `ptr_gap_scan bb n b`,
    `tokens`, `registry`, `B`, `PT`, `TG'`, `saved`, `entries`,
    `[(tokens,registry,B,PT,TG',saved,entries)] ++ snapshots`, `calls`, `ws`] >>
  pure_rewrite_tac[APPEND_ASSOC] >>
  simp[ptr_gap_scan_fields]
QED

Resume ptr_focus_jump_extension[djmp]:
  `?cond ops idx labels. a.po_inst.inst_operands = cond::ops /\
    eval_operand cond at.po_state = SOME idx /\ extract_labels ops = SOME labels /\
    w2n idx < LENGTH labels /\ s' = jump_to (EL (w2n idx) labels) at.po_state` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[concretize_positions_unchanged, step_inst_non_invoke,
          step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[]) >>
  `MEM a.po_inst.inst_opcode [JNZ; DJMP] /\ MEM cond a.po_inst.inst_operands` by simp[] >>
  drule_all ptr_focus_jump_scalar >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
    a.po_state at.po_state` by fs[ptr_paired_sample_def] >>
  drule_all ptr_mixed_vars_eval >>
  simp[ptr_lookup_transport_def, ptr_value_transport_def] >> strip_tac >>
  `eval_operand cond a.po_state = eval_operand cond at.po_state` by
    (Cases_on `eval_operand cond a.po_state` >>
     Cases_on `eval_operand cond at.po_state` >>
     gvs[word_agree_except_bits, fcpTheory.CART_EQ]) >>
  qabbrev_tac `sj = jump_to (EL (w2n idx) labels) a.po_state` >>
  `step_inst fuel C a.po_inst a.po_state = OK sj` by
    simp[step_inst_def, step_inst_base_def, Abbr `sj`] >>
  `sj = jump_to (EL (w2n idx) labels) a.po_state` by simp[Abbr `sj`] >>
  drule_all ptr_paired_selected_jump_entry >>
  disch_then (qx_choose_then `se` (qx_choose_then `b0`
    (qx_choose_then `bb0` strip_assume_tac))) >>
  `MEM a.po_inst.inst_opcode [JMP; JNZ; DJMP]` by simp[] >>
  drule_all ptr_paired_block_prefix_normalize >> strip_tac >>
  qpat_x_assum `zt = ptr_observe _ _ _ _ _ _ _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  qexistsl_tac [`[b] ++ delta`, `ptr_gap_scan bb n b`,
    `tokens`, `registry`, `B`, `PT`, `TG'`, `saved`, `entries`,
    `[(tokens,registry,B,PT,TG',saved,entries)] ++ snapshots`, `calls`, `ws`] >>
  pure_rewrite_tac[APPEND_ASSOC] >>
  simp[ptr_gap_scan_fields]
QED
Finalise ptr_focus_jump_extension
