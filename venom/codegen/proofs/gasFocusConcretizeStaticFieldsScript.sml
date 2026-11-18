Theory gasFocusConcretizeStaticFields
Ancestors
  gasFocusConcretizeTaggedSupport
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrSharedFields
  concretizePtrRequestHistory concretizePtrTaintContent
  concretizePtrOpaqueRetpc concretizePtrValueTransport concretizePtrParamSupport
  concretizeStepStructure concretizeMemLocDefs unitMemInv o1PassContract
  unitTransformDefs ptrDiscipline venomWf venomExecProofs venomExecSemantics
  venomState venomInst memLocDefs passSharedDefs list finite_map pred_set
  concretizePtrChronologicalHistory contextCodegenRel pointerConfinedDefs
  frameHistoryInstructions unitLabelMapIdentity unitShapeDefs

(* Only the current source observation supplies memory safety. Tagged support
   identifies scalar operands without erasing any historical provenance. *)
Theorem ptr_focus_paired_static_fields:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ raw_mem_ok C a.po_fn a.po_inst a.po_state /\
  (?P. EVERY (fn_ptr_ok P) C.ctx_functions) /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst ==>
  w2n at.po_state.vs_initial_fmp <= w2n at.po_state.vs_fmp /\
  dalloca_no_wrap at.po_inst at.po_state
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `a.po_state.vs_initial_fmp = at.po_state.vs_initial_fmp /\
   a.po_state.vs_fmp = at.po_state.vs_fmp` by
    (fs[ptr_paired_sample_def] >> drule ptr_history_content_control >>
     simp[ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def]) >>
  conj_tac >- (fs[raw_mem_ok_def] >> metis_tac[]) >>
  Cases_on `a.po_inst.inst_opcode = DALLOCA`
  >- (`at.po_inst = a.po_inst` by gvs[concretize_positions_unchanged] >>
      `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
         a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
        (fs[ptr_paired_sample_def] >>
         metis_tac[ptr_history_content_labels]) >>
      suspend "dalloca") >>
  `at.po_inst.inst_opcode <> DALLOCA` by
    (rw[concretize_inst_with_positions_def] >> rpt CASE_TAC >>
     gvs[mk_assign_inst_def, mk_nop_inst_def]) >>
  simp[dalloca_no_wrap_def]
QED

Resume ptr_focus_paired_static_fields[dalloca]:
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state` by
    (drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule_all ptr_focus_source_tagged_support >> strip_tac >>
  `ptr_use_ok P (fn_pv P a.po_fn) a.po_inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >>
     metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  simp[dalloca_no_wrap_def] >> rpt strip_tac >>
  `MEM sz_op a.po_inst.inst_operands` by simp[] >>
  `op_taint a.po_taint sz_op = {}` by
    (spose_not_then assume_tac >> fs[taint_ok_def] >>
     first_x_assum drule >> simp[]) >>
  `op_prov TG sz_op = NONE` by
    (Cases_on `sz_op` >> simp[op_prov_def] >>
     spose_not_then assume_tac >>
     `s IN fn_pv P a.po_fn` by
       (Cases_on `FLOOKUP TG s` >> gvs[ptr_static_support_def] >>
        first_x_assum irule >> goal_assum (drule_at Any)) >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_read_ops_def, mem_write_ops_def]) >>
  `eval_operand sz_op a.po_state = eval_operand sz_op at.po_state` by
    (fs[EVERY_MEM] >> drule_all ptr_mixed_vars_eval >>
     Cases_on `eval_operand sz_op a.po_state` >>
     Cases_on `eval_operand sz_op at.po_state` >>
     gvs[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]) >>
  fs[raw_mem_ok_def, dalloca_no_wrap_def]
QED

Finalise ptr_focus_paired_static_fields
