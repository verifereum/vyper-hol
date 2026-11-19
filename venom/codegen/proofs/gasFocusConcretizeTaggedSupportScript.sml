Theory gasFocusConcretizeTaggedSupport
Ancestors
  gasFocusConcretizeTaggedTransfer concretizePtrSourceOwnership
  concretizePtrParamSupport concretizePtrChronologicalHistory
  frameAllocationOwnership ptrDiscipline finite_map list

(* Domain support is independent of numerical provenance erasure and of
   dynamic pointer discipline, including at suspended caller frames. *)
Theorem ptr_focus_source_tagged_support:
  !vs0 C h a tokens registry births PT TG saved.
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions ==>
  MEM a.po_fn C.ctx_functions /\
  ptr_params_ok P a.po_fn PT /\ ptr_static_support P a.po_fn TG /\
  LIST_REL (\tags fr. MEM fr.cf_fn C.ctx_functions /\
    ptr_params_ok P fr.cf_fn (FST tags) /\
    ptr_static_support P fr.cf_fn (SND tags)) saved a.po_stack
Proof
  rewrite_tac[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac ptr_source_ownership_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule ptr_chrono_history_reachable >> strip_tac >>
      gvs[ptr_observation_reachable_def] >>
      drule frame_reachable_functions_member >>
      simp[ptr_params_ok_def, ptr_static_support_def]) >>
  rpt gen_tac >> strip_tac >> ntac 2 disch_tac >>
  irule ptr_focus_tagged_chrono_support >> simp[] >> metis_tac[]
QED
