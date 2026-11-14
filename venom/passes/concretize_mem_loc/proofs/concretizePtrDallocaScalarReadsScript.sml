Theory concretizePtrDallocaScalarReads
Ancestors
  concretizePtrStorageReadProducer concretizePtrIloadFamilyExecution
  concretizePtrDallocaReadChannels concretizePtrOwnerFloor
  concretizePtrTaggedSupport concretizePtrValueTransport lowerDloadPtrSupport
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrStructuralTranscript
  unitLabelMapIdentity o1PassContract unitShapeDefs passSimulationDefs contextCodegenRel codegenRel
  concretizePtrStructuralTrace concretizePtrSourceOwnership
  concretizePtrChronologicalHistory concretizePtrAllocationSize
  concretizePtrDeletedGapHistory concretizePtrOpaqueRetpc
  concretizePtrLedgerAlignment concretizePtrPrefixLedger concretizePtrSharedFields
  concretizeStepStructure concretizeStepShape concretizeStageShape
  ptrDiscipline pointerConfinedDefs opcodeClass memLocDefs venomExecSemantics venomWf venomState
  list finite_map words arithmetic pred_set

Theorem ptr_dalloca_scalar_read_operands[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) /\
  MEM inst.inst_opcode [ILOAD;SLOAD;TLOAD] ==>
  EVERY (\op. ptr_nonopaque_operand fn op /\ op_prov TG op = NONE /\
    op_taint tn op = {}) inst.inst_operands
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >> fs[MEM]) >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `fn_ptr_ok P fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts fn) ==> _`
       (qspec_then `inst` mp_tac) >> fs[MEM] >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  simp[EVERY_MEM] >> gen_tac >> strip_tac >>
  `ptr_nonopaque_operand fn op` by fs[EVERY_MEM] >> simp[] >> conj_tac
  >- (Cases_on `op` >> simp[op_prov_def] >>
      rename1 `FLOOKUP TG u = NONE` >>
      Cases_on `FLOOKUP TG u` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `taint_ok _ _ _ _` mp_tac >> fs[MEM] >>
  simp[taint_ok_def] >> metis_tac[]
QED

Theorem ptr_dalloca_scalar_read_context[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\
  MEM a.po_inst.inst_opcode [ILOAD;SLOAD;TLOAD] ==>
  ?op out. at.po_inst = a.po_inst /\
    a.po_inst.inst_operands = [op] /\ a.po_inst.inst_outputs = [out] /\
    eval_operand op a.po_state = eval_operand op at.po_state /\
    taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
    access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
    op_prov a.po_prov op = NONE
Proof
  strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule concretizePtrOperationalOpcodesTheory.ptr_frame_context_membership >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `inst_wf a.po_inst` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  `?op out. a.po_inst.inst_operands = [op] /\ a.po_inst.inst_outputs = [out]` by
    (fs[MEM] >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  suspend "discipline"
QED

Resume ptr_dalloca_scalar_read_context[discipline]:
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> irule ptr_source_tagged_var_support >>
     rpt (goal_assum (drule_at Any))) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
   access_ok lo a.po_prov a.po_fn a.po_inst a.po_state` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_prov TG op = NONE /\
     op_taint a.po_taint op = {}) a.po_inst.inst_operands` by
    (irule ptr_dalloca_scalar_read_operands >> simp[] >> metis_tac[]) >>
  `a.po_state.vs_labels = at.po_state.vs_labels` by
    (drule ptr_paired_prefix_endpoint >> strip_tac >>
     fs[ptr_paired_sample_def] >> metis_tac[concretizePtrRequestHistoryTheory.ptr_history_content_labels]) >>
  `eval_operand op a.po_state = eval_operand op at.po_state` by
    (drule ptr_paired_prefix_endpoint >> strip_tac >> fs[ptr_paired_sample_def] >>
     gvs[] >> drule_all ptr_mixed_vars_eval >>
     gvs[ptr_lookup_transport_def, ptr_value_transport_scalar_empty] >>
     Cases_on `eval_operand op a.po_state` >>
     Cases_on `eval_operand op at.po_state` >> simp[]) >>
  `at.po_inst = a.po_inst` by suspend "instruction" >>
  qexistsl [`op`,`out`] >> simp[] >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (drule frame_reachable_prov_supported >>
     disch_then (qspec_then `P` mp_tac) >> fs[EVERY_MEM] >> metis_tac[]) >>
  suspend "provenance"
QED

Resume ptr_dalloca_scalar_read_context[provenance]:
  `EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_prov a.po_prov op = NONE /\
     op_taint a.po_taint op = {}) a.po_inst.inst_operands` by
    (irule ptr_dalloca_scalar_read_operands >> simp[] >>
     reverse conj_tac >- metis_tac[] >>
     qexists `P` >> simp[] >> rpt strip_tac >>
     fs[SUBSET_DEF, TO_FLOOKUP] >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
  gvs[]
QED
Resume ptr_dalloca_scalar_read_context[instruction]:
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  qpat_x_assum `ptr_paired_cursor lp a at` mp_tac >>
  simp[ptr_paired_cursor_def] >> strip_tac >>
  `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
    (spose_not_then assume_tac >>
     `a.po_state.vs_inst_idx < EL at.po_state.vs_inst_idx indices` by decide_tac >>
     qpat_x_assum `!k. _ ==> _.inst_opcode = NOP`
       (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[] >>
     qpat_x_assum `a.po_inst = _` SUBST_ALL_TAC >> fs[MEM]) >>
  drule ptr_ledger_alignment_cursor >> strip_tac >>
  first_x_assum (qspec_then `at.po_state.vs_inst_idx` mp_tac) >> simp[] >>
  strip_tac >> fs[MEM] >> gvs[concretize_positions_unchanged]
QED
Finalise ptr_dalloca_scalar_read_context

(* This bound concerns the actual ILOAD descriptor, not arbitrary immutable
   addresses. Pointer discipline excludes provenance on this scalar operand. *)
Theorem ptr_dalloca_scalar_iload_bound[local]:
  inst.inst_opcode = ILOAD /\ inst.inst_operands = [op] /\
  eval_operand op s = SOME x /\ op_prov G op = NONE /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s ==>
  w2n x + 32 <= lo
Proof
  strip_tac >> spose_not_then assume_tac >>
  `MEM (w2n x,32) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def, eval_operands_def] >>
  `?ops v b sz. mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G v = SOME (b,sz) /\ b <= w2n x /\ w2n x+32 <= b+sz` by
    (fs[access_ok_def] >>
     qpat_x_assum `!off len. MEM (off,len) (source_memory_read_ranges inst s) /\ _ ==> _`
       (qspecl_then [`w2n x`,`32`] mp_tac) >> simp[] >>
     `lo < 32+w2n x` by decide_tac >> simp[ADD_COMM]) >>
  gvs[mem_read_ops_def, op_prov_def]
QED

Theorem ptr_dalloca_scalar_read_masks:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\
  ~in_revert_forward a.po_fn a.po_state /\
  (!i. i < lo ==> i IN at.po_taint.t_mem ==> i IN a.po_taint.t_mem) /\
  at.po_taint.t_stor SUBSET a.po_taint.t_stor /\
  at.po_taint.t_trans SUBSET a.po_taint.t_trans /\
  MEM a.po_inst.inst_opcode [ILOAD;SLOAD;TLOAD] /\ ptr_chrono_step C' at zt ==>
  out_taint at.po_taint at.po_inst at.po_state SUBSET
    out_taint a.po_taint a.po_inst a.po_state
Proof
  strip_tac >> drule_all ptr_dalloca_scalar_read_context >> strip_tac >>
  Cases_on `eval_operand op at.po_state` >> gvs[out_taint_def] >>
  rename1 `eval_operand op a.po_state = SOME x` >>
  fs[MEM] >> simp[]
  >- (`w2n x+32 <= lo` by (irule ptr_dalloca_scalar_iload_bound >> metis_tac[]) >>
      simp[mem_word_taint_def, SUBSET_DEF] >> rpt strip_tac >>
      first_x_assum irule >> simp[] >> decide_tac)
  >- (fs[key_taint_def, SUBSET_DEF] >> metis_tac[]) >>
  fs[key_taint_def, SUBSET_DEF] >> metis_tac[]
QED
