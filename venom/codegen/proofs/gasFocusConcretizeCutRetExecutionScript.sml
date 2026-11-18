Theory gasFocusConcretizeCutRetExecution
Ancestors
  gasFocusConcretizeTaggedSupport concretizePtrReturnTransport
  concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrDeletedGapHistory concretizePtrChronologicalHistory
  concretizePtrLedgerAlignment concretizePtrRequestHistory
  concretizePtrOpaqueRetpc concretizeStepStructure ptrDiscipline
  o1LowerDloadGhost o1PassContract
  concretizePtrParamSupport contextCodegenRel unitLabelMapIdentity
  unitShapeDefs venomWf venomExecProofs venomExecSemantics venomState
  venomInst memLocDefs pointerConfinedDefs finite_map list rich_list pred_set

(* A RET's final operand is control, not one of the returned scalars. *)
Theorem ptr_focus_ret_scalar_front[local]:
  MEM i (fn_insts f) /\ i.inst_opcode = RET /\
  i.inst_operands = ops ++ [last] /\ fn_ptr_ok P f /\
  ptr_static_support P f TG /\ taint_ok f tn i s /\ opaque_use_ok f ==>
  EVERY (\op. ptr_nonopaque_operand f op /\ op_prov TG op = NONE /\
              op_taint tn op = {}) ops
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P f) i` by (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `FDOM TG SUBSET fn_pv P f` by
    ((simp[SUBSET_DEF, FLOOKUP_DEF] >> fs[ptr_static_support_def] >> (simp[SUBSET_DEF, FLOOKUP_DEF, ptr_static_support_def]))) >>
  simp[EVERY_MEM] >> qx_gen_tac `op` >> disch_tac >>
  `MEM op i.inst_operands` by simp[] >>
  `op_taint tn op = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     simp[taint_ok_def] >> strip_tac >>
     first_x_assum (qspec_then `op` mp_tac) >> simp[]) >>
  `op_prov TG op = NONE` by metis_tac[ret_operand_no_provenance] >>
  simp[] >> Cases_on `op` >> simp[ptr_nonopaque_operand_def] >>
  rename1 `~retpc_var f v` >> disch_tac >>
  `retpc_use_ok i v` by metis_tac[opaque_use_ok_retpc_use] >>
  gvs[retpc_use_ok_def, APPEND_11_LENGTH]
QED

(* Invert the actual target edge, keeping the resumed caller's binding. *)
Theorem ptr_focus_ret_target_edge[local]:
  at.po_inst.inst_opcode = RET /\ ptr_chrono_step C' at zt ==>
  ?ys tr. eval_operands at.po_inst.inst_operands at.po_state = SOME ys /\
    ys <> [] /\ at.po_stack <> [] /\
    bind_outputs (HD at.po_stack).cf_inst.inst_outputs (FRONT ys)
      (merge_callee_state (HD at.po_stack).cf_state at.po_state) = SOME tr
Proof
  strip_tac >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases, ptr_observe_def] >>
  rpt strip_tac >> gvs[is_terminator_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  metis_tac[adopt_return_fmp_def]
QED

(* The saved calls are aligned at their recorded INVOKE instructions. *)
Theorem ptr_focus_ret_caller_outputs[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  at.po_stack <> [] ==>
  a.po_stack <> [] /\
  (HD a.po_stack).cf_inst.inst_outputs = (HD at.po_stack).cf_inst.inst_outputs
Proof
  strip_tac >>
  drule ptr_paired_prefix_callers >> simp[ptr_paired_callers_def] >> strip_tac >>
  `0 < LENGTH calls /\ a.po_stack <> []` by
    (Cases_on `at.po_stack` >> Cases_on `a.po_stack` >> gvs[]) >>
  conj_tac >- simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
  Cases_on `HD calls` >> simp[ptr_paired_call_def] >> strip_tac >>
  `r < LENGTH ht` by
    (drule ptr_paired_prefix_samples >> simp[ptr_paired_samples_def, ptr_sample_list_def]) >>
  drule_all ptr_paired_prefix_alignment >> simp[EL_APPEND_EQN] >> strip_tac >>
  qpat_x_assum `ptr_paired_cursor _ _ _` mp_tac >>
  simp[ptr_paired_cursor_def] >> strip_tac >>
  drule ptr_ledger_alignment_cursor >> strip_tac >>
  `((EL (EL r done) h).po_state.vs_inst_idx) =
    EL (EL r ht).po_state.vs_inst_idx indices` by
    (qpat_x_assum `!k. _ <= k /\ _ ==> _`
       (qspec_then `(EL (EL r done) h).po_state.vs_inst_idx` mp_tac) >>
     gvs[] >> decide_tac) >>
  qpat_x_assum `!j. j < LENGTH bbt.bb_instructions ==> _`
    (qspec_then `(EL r ht).po_state.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[concretize_positions_unchanged, ptr_paired_frame_def]
QED

Theorem ptr_focus_ret_execution:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ (?P. EVERY (fn_ptr_ok P) C.ctx_functions) /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  a.po_inst.inst_opcode = RET /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?ret sr tr.
    step_inst 0 C a.po_inst a.po_state = IntRet ret a.po_state /\
    step_inst 0 C' at.po_inst at.po_state = IntRet ret at.po_state /\
    ret.iret_adopt_fmp = NONE /\
    a.po_stack <> [] /\ at.po_stack <> [] /\
    (HD a.po_stack).cf_inst.inst_outputs = (HD at.po_stack).cf_inst.inst_outputs /\
    bind_outputs (HD a.po_stack).cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state (HD a.po_stack).cf_state a.po_state)) = SOME sr /\
    bind_outputs (HD at.po_stack).cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state (HD at.po_stack).cf_state at.po_state)) = SOME tr
Proof
  strip_tac >>
  `at.po_inst = a.po_inst /\ at.po_inst.inst_opcode = RET` by
    simp[concretize_positions_unchanged] >>
  drule_all ptr_focus_ret_target_edge >> strip_tac >>
  drule_all ptr_focus_ret_caller_outputs >> strip_tac >>
  `a.po_inst.inst_operands <> []` by
    (Cases_on `a.po_inst.inst_operands` >> gvs[eval_operands_def]) >>
  qabbrev_tac `ops = FRONT a.po_inst.inst_operands` >>
  qabbrev_tac `last = LAST a.po_inst.inst_operands` >>
  `a.po_inst.inst_operands = ops ++ [last]` by
    simp[Abbr `ops`, Abbr `last`, APPEND_FRONT_LAST] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule_all ptr_focus_source_tagged_support >> strip_tac >>
  `fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def] >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >>
     fs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  drule_all ptr_focus_ret_scalar_front >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
    a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  `eval_operands (ops ++ [last]) at.po_state = SOME ys` by metis_tac[] >>
  drule_all ptr_mixed_return_front >> strip_tac >>
  qexists_tac `<|iret_values := FRONT ys; iret_adopt_fmp := NONE|>` >>
  `eval_operands a.po_inst.inst_operands a.po_state = SOME xs` by metis_tac[] >>
  Cases_on `xs` >> Cases_on `ys` >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, adopt_return_fmp_def] >>
  qpat_x_assum `bind_outputs _ _ _ = SOME tr` mp_tac >>
  simp[bind_outputs_def] >> strip_tac >> simp[]
QED
