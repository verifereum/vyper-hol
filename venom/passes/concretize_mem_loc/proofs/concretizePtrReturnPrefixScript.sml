Theory concretizePtrReturnPrefix
Ancestors concretizePtrReturnProduction concretizePtrPairedPrefix
  concretizePtrPairedFields concretizePtrHistoricalPlacement
  concretizePtrReturnTransport concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrSourceOwnership
  concretizePtrMixedAllocationPrefix concretizePtrValueSelection
  concretizeStepStructure venomExecSemantics venomState venomInst venomWf
  ptrDiscipline finite_map list rich_list pred_set

Theorem ptr_ret_prefix_control[local]:
  ptr_chrono_step C a b /\ a.po_inst.inst_opcode = RET ==>
  b.po_fn = (HD a.po_stack).cf_fn /\ b.po_stack = TL a.po_stack /\
  b.po_state.vs_params = (HD a.po_stack).cf_state.vs_params
Proof
  simp[Once concretizePtrChronologicalHistoryTheory.ptr_chrono_step_cases,
       concretizePtrChronologicalHistoryTheory.ptr_observe_def] >>
  rpt strip_tac >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_opcode_eqs,
       AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  qspec_then `(\s. s.vs_params)` mp_tac venomInstProofs1Theory.bind_outputs_preserves >>
  simp[update_var_def] >> disch_then drule >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem ptr_paired_ret_prefix_immediate:
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
  a.po_inst.inst_opcode = RET /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?b PTc TGc outs B'.
    HD saved = (PTc,TGc) /\
    outs = (HD a.po_stack).cf_inst.inst_outputs /\
    B' = ptr_birth_overlay (HD (TL tokens)) b.po_state.vs_allocas births /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [b]) b (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      (TL tokens) registry B' PTc (DRESTRICT TGc (COMPL (set outs)))
      (TL saved) entries
      (H ++ [(TL tokens,registry,B',PTc,DRESTRICT TGc (COMPL (set outs)),TL saved,entries)])
      (TL calls) ws
Proof
  strip_tac >> drule_all ptr_paired_ret_successor_births >> strip_tac >>
  `at.po_inst.inst_opcode = RET` by
    gvs[concretize_positions_unchanged] >>
  drule ptr_tagged_chrono_step_projection >> strip_tac >>
  `b.po_fn = (HD a.po_stack).cf_fn /\
   b.po_state.vs_params = (HD a.po_stack).cf_state.vs_params` by
    metis_tac[ptr_ret_prefix_control] >>
  `zt.po_fn = (HD at.po_stack).cf_fn /\ zt.po_stack = TL at.po_stack /\
   zt.po_state.vs_params = (HD at.po_stack).cf_state.vs_params` by
    metis_tac[ptr_ret_prefix_control] >>
  qpat_x_assum `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    mp_tac >> pure_rewrite_tac[ptr_paired_prefix_def] >> strip_tac >>
  qexistsl_tac [`b`, `PTc`, `TGc`, `outs`, `B'`] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[ptr_paired_prefix_def] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule ptr_paired_samples_pair >>
      simp[ptr_paired_sample_def]) >>
  conj_tac >- suspend "alignment" >>
  conj_tac >- suspend "callers" >>
  suspend "writes"
QED

Resume ptr_paired_ret_prefix_immediate[alignment]:
  irule ptr_paired_alignment_pair >>
  rpt (goal_assum (drule_at Any)) >>
  `0 < LENGTH calls` by
    (fs[ptr_paired_callers_def] >> Cases_on `a.po_stack` >> gvs[]) >>
  qpat_assum `ptr_paired_callers _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_paired_callers_def] >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
  Cases_on `HD calls` >>
  simp[ptr_paired_call_def, ptr_paired_frame_def] >> strip_tac >>
  qpat_assum `ptr_paired_alignment _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_paired_alignment_def] >>
  disch_then (qspec_then `r` mp_tac) >>
  `r < LENGTH ht` by (fs[ptr_paired_samples_def, ptr_sample_list_def] >> decide_tac) >>
  simp[EL_APPEND_EQN] >> strip_tac >>
  qabbrev_tac `snap = EL q H` >> PairCases_on `snap` >>
  `snap3 = PTc /\ snap4 = TGc` by
    fs[ptr_paired_saved_tags_def] >>
  `q < LENGTH h` by (fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >> metis_tac[]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!key site. FLOOKUP snap2 key = SOME site ==> FLOOKUP B' key = SOME site` by
    (rpt strip_tac >>
     qpat_assum `ptr_structural_transcript _ _ _ _ (_ ++ [_]) _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac ptr_transcript_birth_retained) >>
     disch_then (qspecl_then [`LENGTH h`, `q`] mp_tac) >>
     `LENGTH H = LENGTH h` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
     simp[EL_APPEND_EQN]) >>
  gvs[markerTheory.Abbrev_def] >>
  qpat_x_assum `(_,_,_,_,_,_,_) = EL _ H` (assume_tac o SYM) >>
  qpat_x_assum `ptr_paired_params _ _ _ _` mp_tac >>
  simp[ptr_paired_params_def] >>
  strip_tac >- simp[] >>
  disj2_tac >>
  irule concretizePtrAllocationTransportTheory.ptr_args_transport_birth_extension >>
  goal_assum (drule_at Any) >>
  simp[]
QED

Resume ptr_paired_ret_prefix_immediate[callers]:
  qpat_x_assum `ptr_paired_callers _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_paired_callers_def] >> strip_tac >>
  simp[ptr_paired_callers_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC k` mp_tac) >>
  `SUC k < LENGTH calls` by fs[LENGTH_TL] >>
  simp[] >>
  Cases_on `EL (SUC k) calls` >> strip_tac >>
  `EL k (TL calls) = (q,r)` by (Cases_on `calls` >> gvs[]) >>
  `EL k (TL a.po_stack) = EL (SUC k) a.po_stack /\
   EL k (TL at.po_stack) = EL (SUC k) at.po_stack /\
   EL k (TL saved) = EL (SUC k) saved` by
    (Cases_on `a.po_stack` >> Cases_on `at.po_stack` >> Cases_on `saved` >> gvs[]) >>
  simp[] >> irule ptr_paired_call_retained >>
  goal_assum (drule_at Any) >>
  fs[ptr_paired_call_def, ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >>
  metis_tac[]
QED

Resume ptr_paired_ret_prefix_immediate[writes]:
  qpat_assum `ptr_structural_transcript _ _ _ _ h a _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any assume_tac ptr_structural_transcript_erasure) >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `LAST h = a` by metis_tac[concretizePtrChronologicalHistoryTheory.ptr_chrono_history_end] >>
  `EVERY (\n. SUC n < LENGTH h) done` by
    (qpat_x_assum `ptr_event_embedding _ _ _` mp_tac >>
     simp[concretizePtrEventEmbeddingTheory.ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN] >> decide_tac) >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM listTheory.APPEND_NIL))) >>
  irule ptr_paired_writes_pair >>
  fs[ptr_paired_samples_def, ptr_sample_list_def, is_terminator_def]
QED

Finalise ptr_paired_ret_prefix_immediate
