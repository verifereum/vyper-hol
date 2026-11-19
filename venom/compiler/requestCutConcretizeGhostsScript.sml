Theory requestCutConcretizeGhosts
Ancestors
  lowerDloadDefs unitTransformDefs
  concretizePtrDallocaGhostHistory concretizePtrDallocaGhostInterface
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrEventEmbedding
  concretizePtrPairedPrefix o1PassContract list arithmetic

Theorem request_cut_concretize_ghost_masks:
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C Ct /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom Ct = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  EVERY (\n. ~in_revert_forward (EL n h).po_fn (EL n h).po_state) done ==>
  at.po_taint.t_stor SUBSET a.po_taint.t_stor /\
  at.po_taint.t_trans SUBSET a.po_taint.t_trans
Proof
  strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `h <> [] /\ LAST h = a` by metis_tac[ptr_chrono_history_end] >>
  `ht <> [] /\ LAST ht = at` by metis_tac[ptr_chrono_history_end] >>
  `LENGTH H = LENGTH h /\ 0 < LENGTH h /\ LENGTH ht = SUC (LENGTH done)` by
    fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  `H <> []` by (strip_tac >> gvs[]) >>
  `LENGTH h - 1 < LENGTH h /\ LENGTH ht - 1 = LENGTH done /\
   LENGTH H - 1 = LENGTH h - 1` by decide_tac >>
  `EL (LENGTH done) ht = at /\ EL (LENGTH h - 1) h = a /\
   EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (qpat_x_assum `LAST ht = at` mp_tac >>
     qpat_x_assum `LAST h = a` mp_tac >>
     qpat_x_assum `LAST H = _` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `LENGTH done = 0 \/ EL (LENGTH done - 1) done < LENGTH h - 1` by
    (Cases_on `LENGTH done = 0` >- fs[] >>
     `LENGTH done - 1 < LENGTH done` by decide_tac >>
     qpat_assum `ptr_event_embedding h ht (done ++ [LENGTH h - 1])`
       (mp_tac o List.last o CONJUNCTS o REWRITE_RULE [ptr_event_embedding_def]) >>
     disch_then (qspecl_then [`LENGTH done - 1`,`LENGTH done`] mp_tac) >>
     fs[EL_APPEND_EQN]) >>
  `LENGTH h - 1 <= EL (LENGTH done) (done ++ [LENGTH h - 1])` by
    simp[EL_APPEND_EQN] >>
  mp_tac (Q.INST [`endpoint` |-> `a`, `C'` |-> `Ct`] ptr_dalloca_ghost_history_static) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`LENGTH h - 1`,`LENGTH done`] mp_tac) >>
  (impl_tac >- fs[]) >>
  disch_then (qspecl_then [`tokens`,`registry`,`births`,`PT`,`TG`,`saved`,`entries`] mp_tac) >>
  simp[ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def] >>
  strip_tac >> simp[]
QED
