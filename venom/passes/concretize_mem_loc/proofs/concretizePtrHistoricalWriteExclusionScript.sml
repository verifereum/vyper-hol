Theory concretizePtrHistoricalWriteExclusion
Ancestors
  concretizePtrPairedPrefix concretizePtrHistoricalWriteClassification
  concretizePtrDemandWriteExclusion concretizePtrWritePurity
  concretizePtrOpaqueRetpc concretizePtrChronologicalHistory
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrEventEmbedding concretizePtrLedgerAlignment concretizePtrPairedFields
  concretizePtrOperationalOpcodes
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape
  venomExecSemantics venomWf unitShapeDefs ptrDiscipline finite_map list
  stackPlanGen unitMemInv

Theorem ptr_trace_departed_inst_ids:
  !R vs C Ct h a ht at done tokens registry births PT TG saved entries.
  ptr_structural_trace R vs C Ct h a ht at done tokens registry births PT TG saved entries ==>
  !q. q < LENGTH done ==>
    (EL (EL q done) h).po_inst.inst_id = (EL q ht).po_inst.inst_id
Proof
  ho_match_mp_tac ptr_structural_trace_strongind >> rpt conj_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- simp[]
  >- (rpt strip_tac >>
      drule ptr_structural_trace_embedding >>
      simp[ptr_event_embedding_def, EVERY_MEM] >> strip_tac >>
      `EL q done < LENGTH h` by
        (first_x_assum irule >> simp[MEM_EL] >> qexists_tac `q` >> simp[]) >>
      simp[EL_APPEND_EQN]) >>
  rpt strip_tac >>
  Cases_on `q < LENGTH done`
  >- (drule ptr_structural_trace_embedding >>
      simp[ptr_event_embedding_def, EVERY_MEM] >> strip_tac >>
      `EL q done < LENGTH h` by
        (first_x_assum irule >> simp[MEM_EL] >> qexists_tac `q` >> simp[]) >>
      simp[EL_APPEND_EQN]) >>
  `q = LENGTH done` by fs[] >> gvs[] >>
  (drule ptr_structural_trace_source >>
   disch_then (mp_tac o MATCH_MP ptr_chrono_history_end) >> strip_tac >>
   drule ptr_structural_trace_target >>
   disch_then (mp_tac o MATCH_MP ptr_chrono_history_end) >> strip_tac >>
   drule ptr_structural_trace_embedding >> strip_tac >>
   `0 < LENGTH h` by (Cases_on `h` >> fs[]) >>
   `LENGTH done = LENGTH ht - 1` by decide_tac >>
   fs[EL_APPEND_EQN] >>
   `LENGTH h - 1 = PRE (LENGTH h) /\
    LENGTH ht - 1 = PRE (LENGTH ht)` by decide_tac >>
   metis_tac[LAST_EL])
QED

Theorem ptr_departed_cursor_instruction:
  ptr_paired_cursor lp a at /\ fn_inst_ids_distinct a.po_fn /\
  a.po_inst.inst_id = at.po_inst.inst_id ==>
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst
Proof
  simp[ptr_paired_cursor_def] >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (fs[fn_inst_ids_distinct_def] >>
     `?xs ys. a.po_fn.fn_blocks = xs ++ bb::ys` by metis_tac[MEM_SPLIT] >>
     gvs[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]) >>
  drule ptr_ledger_alignment_cursor >> strip_tac >>
  `EL at.po_state.vs_inst_idx indices < LENGTH bb.bb_instructions /\
   EL at.po_state.vs_inst_idx bbt.bb_instructions =
     concretize_inst_with_positions (lp a.po_fn)
       (EL (EL at.po_state.vs_inst_idx indices) bb.bb_instructions)` by
    (qpat_x_assum `!j. j < LENGTH bbt.bb_instructions ==> _`
       (qspec_then `at.po_state.vs_inst_idx` mp_tac) >> simp[]) >>
  `a.po_state.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
    (drule ALL_DISTINCT_EL_IMP >>
     disch_then (qspecl_then [`a.po_state.vs_inst_idx`,
       `EL at.po_state.vs_inst_idx indices`] mp_tac) >>
     simp[EL_MAP] >>
     gvs[concretize_positions_inst_id]) >>
  gvs[]
QED

Theorem ptr_paired_historical_event:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  w < EL q done /\ q < LENGTH done ==>
  ?tsj rj bj PTj TGj sj ej next.
    EL (EL q done) H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
    next = EL (SUC (EL q done)) H /\
    SUC (EL q done) < LENGTH h /\ SUC q < LENGTH ht /\
    ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry
      births PT TG saved entries H /\ ptr_stage_placements C' positions /\
    ptr_snapshot_step C (TAKE (SUC (EL q done)) h)
      (EL (EL q done) h) (EL (SUC (EL q done)) h)
      (tsj,rj,bj,PTj,TGj,sj,ej) next /\
    ptr_mixed_vars bj positions TGj (EL (EL q done) h).po_taint
      (EL (EL q done) h).po_fn (EL q ht).po_fn
      (EL (EL q done) h).po_state (EL q ht).po_state /\
    ptr_core_shared (EL (EL q done) h).po_state (EL q ht).po_state /\
    ptr_observation_reachable vs C (EL (EL q done) h) /\
    access_ok lo (EL (EL q done) h).po_prov (EL (EL q done) h).po_fn
      (EL (EL q done) h).po_inst (EL (EL q done) h).po_state /\
    taint_ok (EL (EL q done) h).po_fn (EL (EL q done) h).po_taint
      (EL (EL q done) h).po_inst (EL (EL q done) h).po_state /\
    ~in_revert_forward (EL (EL q done) h).po_fn (EL (EL q done) h).po_state /\
    (EL q ht).po_inst = concretize_inst_with_positions
      (lp (EL (EL q done) h).po_fn) (EL (EL q done) h).po_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `q < LENGTH ht` by fs[ptr_paired_samples_def] >>
  drule_all ptr_paired_prefix_alignment >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_paired_prefix_placements >> strip_tac >>
  `SUC q < LENGTH ht` by fs[ptr_paired_samples_def] >>
  `EL q (done ++ [LENGTH h - 1]) = EL q done` by
    simp[EL_APPEND_EQN] >>
  gvs[] >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_nop_interval >>
  disch_then (qspec_then `q` mp_tac) >> simp[] >> strip_tac >>
  `SUC (EL q done) < LENGTH h` by decide_tac >>
  drule ptr_structural_transcript_adjacent >>
  disch_then (qspec_then `EL q done` mp_tac) >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_snapshot_step C pre aa bb snapshot snapshot'` >>
  PairCases_on `snapshot` >> PairCases_on `snapshot'` >>
  gvs[ptr_snapshot_step_def] >>
  `ptr_mixed_vars snapshot2 positions snapshot4 aa.po_taint aa.po_fn
      (EL q ht).po_fn aa.po_state (EL q ht).po_state` by
    (qpat_x_assum `ptr_paired_samples _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_paired_samples_def] >> strip_tac >>
     qpat_x_assum `!j. j < LENGTH ht ==> _` (qspec_then `q` mp_tac) >>
     simp[ptr_paired_sample_def, Abbr `aa`]) >>
  `ptr_core_shared aa.po_state (EL q ht).po_state` by
    (drule ptr_paired_samples_core >>
     disch_then (qspec_then `q` mp_tac) >> simp[Abbr `aa`]) >>
  `ptr_observation_reachable vs C aa` by
    (drule ptr_structural_trace_source >>
     disch_then (mp_tac o MATCH_MP ptr_chrono_history_reachable) >>
     simp[EVERY_MEM] >> strip_tac >>
     first_x_assum irule >> simp[Abbr `aa`, MEM_EL] >>
     qexists_tac `EL q done` >> simp[]) >>
  `access_ok lo aa.po_prov aa.po_fn aa.po_inst aa.po_state /\
   taint_ok aa.po_fn aa.po_taint aa.po_inst aa.po_state` by
    (fs[ptr_observation_reachable_def, ptr_discipline_def] >>
     qpat_x_assum `!stk PG G tn fn inst s. frame_reachable _ _ _ _ _ _ _ _ _ ==> _`
       drule >> simp[]) >>
  `~in_revert_forward aa.po_fn aa.po_state` by
    (qhdtm_x_assum `ptr_demand_interval` mp_tac >>
     simp[ptr_demand_interval_def] >> strip_tac >>
     qpat_x_assum `!j. w <= j /\ j < LENGTH h ==> _`
       (qspec_then `EL q done` mp_tac) >> simp[Abbr `aa`]) >>
  `aa.po_inst.inst_id = (EL q ht).po_inst.inst_id` by
    (drule ptr_trace_departed_inst_ids >>
     disch_then (qspec_then `q` mp_tac) >> simp[Abbr `aa`]) >>
  `MEM aa.po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> simp[]) >>
  `fn_inst_ids_distinct aa.po_fn` by
    (qhdtm_x_assum `ptr_demand_interval` mp_tac >>
     simp[ptr_demand_interval_def] >> strip_tac >>
     fs[EVERY_MEM, wf_function_def]) >>
  `(EL q ht).po_inst = concretize_inst_with_positions (lp aa.po_fn) aa.po_inst` by
    (irule ptr_departed_cursor_instruction >> simp[]) >>
  simp[ptr_snapshot_step_def]
QED
