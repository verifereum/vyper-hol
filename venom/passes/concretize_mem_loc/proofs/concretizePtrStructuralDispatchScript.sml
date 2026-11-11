Theory concretizePtrStructuralDispatch
Ancestors concretizePtrMixedAllocationPrefix concretizePtrReturnPrefix
  concretizePtrPairedPrefixProbe concretizePtrPairedPrefix
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrOperationalOpcodes
  concretizePtrUniversalStepSchema concretizeStepStructure
  o1PassContract stackPlanGen ptrDiscipline unitMemInv venomWf cfgWf
  o1ScheduleDecomp venomExecSemantics venomInst list finite_map

Theorem ptr_paired_structural_prefix_normalize:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\
  (a.po_inst.inst_opcode = ALLOCA \/ a.po_inst.inst_opcode = RET) ==>
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
  `?b ts reg B P G sv en snap cs ledger.
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [b]) b (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      ts reg B P G sv en (H ++ [snap]) cs ledger` by
    (qpat_x_assum `_ = ALLOCA \/ _ = RET` strip_assume_tac
     >- suspend "alloca"
     >> drule_all ptr_paired_ret_prefix_immediate >> strip_tac >>
     rpt (goal_assum (drule_at Any))) >>
  `fn_inst_wf b.po_fn` by
    (qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ (_ ++ [_]) _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac ptr_paired_prefix_transcript) >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_reachable >> strip_tac >>
     fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> strip_tac >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ (_ ++ [_]) _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac ptr_paired_prefix_normalize) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`[b] ++ delta`, `ptr_gap_scan bb (LENGTH delta) b`, `ts`, `reg`, `B`, `P`, `G`, `sv`, `en`, `[snap] ++ snapshots`, `cs`, `ledger`] >>
  simp[APPEND_ASSOC, concretizePtrDeletedGapHistoryTheory.ptr_gap_scan_fields]
QED

Resume ptr_paired_structural_prefix_normalize[alloca]:
  `fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_reachable >> strip_tac >>
     fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> strip_tac >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_paired_prefix_alloca_immediate >> strip_tac >>
  rpt (goal_assum (drule_at Any))
QED

Finalise ptr_paired_structural_prefix_normalize
