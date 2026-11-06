Theory concretizePtrPairedCallEntry
Ancestors
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizePtrSourceOwnership
  concretizePtrOpaqueRetpc concretizePtrSharedFields concretizePtrValueTransport
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape
  contextCodegenRel unitLabelMapIdentity
  ptrDiscipline venomExecSemantics venomExecProofs venomWf venomState list finite_map

Theorem ptr_owned_invoke_restrictions:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  ptr_discipline lo C vs0 /\ opaque_use_ok a.po_fn /\
  a.po_inst.inst_opcode = INVOKE /\
  decode_invoke a.po_inst = SOME (nm,ops) ==>
  EVERY (ptr_nonopaque_operand a.po_fn) ops /\
  MAP (op_taint a.po_taint) ops = REPLICATE (LENGTH ops) {}
Proof
  strip_tac >>
  drule ptr_gap_ownership_history >> strip_tac >>
  drule ptr_chrono_history_reachable >> strip_tac >>
  gvs[ptr_observation_reachable_def] >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >> gvs[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >>
     metis_tac[lookup_block_MEM, MEM_EL]) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `a.po_inst.inst_operands = Label nm :: ops` by
    (gvs[decode_invoke_def, AllCaseEqs()]) >>
  conj_tac
  >- (`~MEM a.po_inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by simp[] >>
      drule_all ptr_nonopaque_instruction_operands >> simp[]) >>
  `EVERY (\op. op_taint a.po_taint op = {}) ops` by
    (gvs[EVERY_MEM, taint_ok_def] >> metis_tac[]) >>
  pop_assum mp_tac >>
  qpat_x_assum `decode_invoke _ = _` kall_tac >>
  qpat_x_assum `a.po_inst.inst_operands = _` kall_tac >>
  Induct_on `ops` >> simp[]
QED

Theorem ptr_paired_invoke_args:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_discipline lo C vs0 /\ opaque_use_ok a.po_fn /\
  a.po_inst.inst_opcode = INVOKE /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  decode_invoke at.po_inst = SOME (nm,ops) /\
  eval_operands ops at.po_state = SOME argst ==>
  decode_invoke a.po_inst = SOME (nm,ops) /\
  EVERY (ptr_nonopaque_operand a.po_fn) ops /\
  MAP (op_taint a.po_taint) ops = REPLICATE (LENGTH ops) {} /\
  ?args. eval_operands ops a.po_state = SOME args /\
    ptr_args_transport births positions (MAP (op_prov TG) ops)
      (REPLICATE (LENGTH args) {}) args argst
Proof
  strip_tac >>
  `at.po_inst = a.po_inst` by simp[concretize_positions_unchanged] >>
  `decode_invoke a.po_inst = SOME (nm,ops)` by metis_tac[] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule_all ptr_owned_invoke_restrictions >> strip_tac >>
  simp[] >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `a.po_state.vs_labels = at.po_state.vs_labels` by
    fs[ptr_paired_sample_def, ptr_core_shared_def, ptr_shared_fields_def] >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
    a.po_state at.po_state` by fs[ptr_paired_sample_def] >>
  drule_all ptr_mixed_vars_eval_operands >>
  Cases_on `eval_operands ops a.po_state` >> simp[] >>
  strip_tac >> drule ptr_args_transport_lengths >> simp[] >>
  strip_tac >> gvs[]
QED
