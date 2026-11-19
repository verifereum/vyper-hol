Theory gasFocusConcretizeInvokeSuccessor
Ancestors
  gasFocusConcretizeInvokeRestrictions concretizePtrPairedCallRestricted
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrChronologicalHistory
  concretizePtrDeletedGapHistory concretizePtrOperationalOpcodes
  concretizeStepStructure ptrDiscipline
  venomExecSemantics venomInst venomWf finite_map list

(* Invert the observed target call before normalizing its source callee. *)
Theorem ptr_focus_invoke_successor:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
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
  ?ops f b B bb n delta snapshots.
    (?nm. decode_invoke a.po_inst = SOME (nm,ops) /\
          lookup_function nm C.ctx_functions = SOME f) /\
    lookup_block b.po_state.vs_current_bb b.po_fn.fn_blocks = SOME bb /\
    LENGTH delta = n /\ LENGTH snapshots = n /\
    ptr_paired_prefix R lp positions lo vs C C'
      ((h ++ [b]) ++ delta) (ptr_gap_scan bb n b) (ht ++ [zt]) zt
      (done ++ [LENGTH h - 1])
      (LENGTH h :: tokens) (registry |+ (LENGTH h,f)) B
      (MAP (op_prov TG) ops) FEMPTY ((PT,TG)::saved)
      (entries |+ (LENGTH h,LENGTH ht))
      ((H ++ [(LENGTH h :: tokens,registry |+ (LENGTH h,f),B,
        MAP (op_prov TG) ops,FEMPTY,((PT,TG)::saved),
        entries |+ (LENGTH h,LENGTH ht))]) ++ snapshots)
      ((LENGTH h - 1,LENGTH ht - 1)::calls) ws /\
    (ptr_gap_scan bb n b).po_fn = f /\
    (ptr_gap_scan bb n b).po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp f)
      (ptr_gap_scan bb n b).po_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `opaque_use_ok a.po_fn` by
    (drule ptr_chrono_history_reachable >>
     simp[ptr_observation_reachable_def] >> strip_tac >>
     drule ptr_frame_context_membership >> strip_tac >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. first_block_no_phi f /\ fn_inst_wf f /\
    EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `at.po_inst = a.po_inst` by simp[concretize_positions_unchanged] >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_def, AllCaseEqs()]) >>
  `zt = ptr_observe
    (<|cf_fn := at.po_fn; cf_inst := at.po_inst; cf_state := at.po_state;
       cf_params := at.po_params; cf_prov := at.po_prov;
       cf_tvar := at.po_taint.t_var|> :: at.po_stack)
    (MAP (op_prov at.po_prov) ops) FEMPTY
    (at.po_taint with t_var := FEMPTY) zt.po_fn zt.po_inst zt.po_state` by
    simp[ptr_observe_def, ptr_observation_component_equality] >>
  `decode_invoke at.po_inst = SOME (nm,ops) /\
   active_inst at.po_fn at.po_inst at.po_state /\
   at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst` by simp[] >>
  drule_all ptr_focus_invoke_restrictions >> strip_tac >>
  drule_all ptr_paired_invoke_prefix_normalize_restricted >> strip_tac >>
  qexistsl_tac [`b`, `B`, `bb`, `delta`, `snapshots`] >>
  qpat_x_assum `zt = ptr_observe _ _ _ _ _ _ _` kall_tac >>
  gvs[ptr_gap_scan_fields, ptr_observe_def]
QED
