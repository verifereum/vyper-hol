Theory concretizePtrPairedCallSchema
Ancestors
  concretizePtrPairedCallEntry concretizePtrPairedPrefixProbe
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrSourceOwnership
  concretizePtrActivationBirths concretizePtrActivationChronology
  concretizePtrDeletedGapHistory venomExecSemantics venomWf unitShapeDefs
  concretizePtrChronologicalHistory concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrEventEmbedding
  concretizeStepStructure concretizeStepShape
  concretizePtrValueSelection concretizePtrValueTransport concretizePtrOpaqueRetpc
  venomState venomInst rich_list arithmetic
  ptrDiscipline finite_map list

Theorem ptr_paired_invoke_prefix_normalize:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_discipline lo C vs0 /\ opaque_use_ok a.po_fn /\
  a.po_inst.inst_opcode = INVOKE /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  decode_invoke at.po_inst = SOME (nm,ops) /\
  eval_operands ops at.po_state = SOME argst /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  EVERY (\f. first_block_no_phi f /\ fn_inst_wf f /\
    EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
    (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation inst.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) Ct.ctx_functions /\
  lookup_function nm Ct.ctx_functions = SOME g /\
  active_inst at.po_fn at.po_inst at.po_state /\
  setup_callee g argst at.po_state = SOME ct /\ enters_block g ct ct' /\
  active_inst g it ct' /\
  bt = ptr_observe
    (<|cf_fn := at.po_fn; cf_inst := at.po_inst; cf_state := at.po_state;
       cf_params := at.po_params; cf_prov := at.po_prov;
       cf_tvar := at.po_taint.t_var|> :: at.po_stack)
    (MAP (op_prov at.po_prov) ops) FEMPTY
    (at.po_taint with t_var := FEMPTY) g it ct' /\
  ptr_chrono_step Ct at bt ==>
  ?f args cs cs' i b B bb n delta snapshots.
    lookup_function nm C.ctx_functions = SOME f /\
    eval_operands ops a.po_state = SOME args /\
    setup_callee f args a.po_state = SOME cs /\ enters_block f cs cs' /\
    active_inst f i cs' /\
    b = ptr_observe
      (<|cf_fn := a.po_fn; cf_inst := a.po_inst; cf_state := a.po_state;
         cf_params := a.po_params; cf_prov := a.po_prov;
         cf_tvar := a.po_taint.t_var|> :: a.po_stack)
      (MAP (op_prov a.po_prov) ops) FEMPTY
      (a.po_taint with t_var := FEMPTY) f i cs' /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved
      (MAP (op_prov TG) ops) FEMPTY ((PT,TG)::saved) /\
    B = ptr_birth_overlay (LENGTH h) b.po_state.vs_allocas births /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      (h ++ [b]) b (ht ++ [bt]) bt (done ++ [LENGTH h - 1])
      (LENGTH h :: tokens) (registry |+ (LENGTH h,f)) B
      (MAP (op_prov TG) ops) FEMPTY ((PT,TG)::saved)
      (entries |+ (LENGTH h,LENGTH ht))
      (H ++ [(LENGTH h :: tokens,registry |+ (LENGTH h,f),B,
        MAP (op_prov TG) ops,FEMPTY,((PT,TG)::saved),
        entries |+ (LENGTH h,LENGTH ht))])
      ((LENGTH h - 1,LENGTH ht - 1)::calls) ws /\
    lookup_block b.po_state.vs_current_bb b.po_fn.fn_blocks = SOME bb /\
    LENGTH delta = n /\ LENGTH snapshots = n /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      ((h ++ [b]) ++ delta) (ptr_gap_scan bb n b) (ht ++ [bt]) bt
      (done ++ [LENGTH h - 1])
      (LENGTH h :: tokens) (registry |+ (LENGTH h,f)) B
      (MAP (op_prov TG) ops) FEMPTY ((PT,TG)::saved)
      (entries |+ (LENGTH h,LENGTH ht))
      ((H ++ [(LENGTH h :: tokens,registry |+ (LENGTH h,f),B,
        MAP (op_prov TG) ops,FEMPTY,((PT,TG)::saved),
        entries |+ (LENGTH h,LENGTH ht))]) ++ snapshots)
      ((LENGTH h - 1,LENGTH ht - 1)::calls) ws /\
    (ptr_gap_scan bb n b).po_inst.inst_opcode <> NOP /\
    bt.po_inst = concretize_inst_with_positions (lp f)
      (ptr_gap_scan bb n b).po_inst
Proof
  strip_tac >> drule_all ptr_paired_invoke_entry >> strip_tac >>
  qabbrev_tac `b = ptr_observe
    (<|cf_fn := a.po_fn; cf_inst := a.po_inst; cf_state := a.po_state;
       cf_params := a.po_params; cf_prov := a.po_prov;
       cf_tvar := a.po_taint.t_var|> :: a.po_stack)
    (MAP (op_prov a.po_prov) ops) FEMPTY
    (a.po_taint with t_var := FEMPTY) f i cs'` >>
  `fn_inst_wf f` by
    (fs[EVERY_MEM] >> metis_tac[venomInstTheory.lookup_function_MEM]) >>
  `ptr_tagged_chrono_step C (HD tokens) a b PT TG saved
    (MAP (op_prov TG) ops) FEMPTY ((PT,TG)::saved)` by suspend "tagged" >>
  `ptr_birth_overlay (LENGTH h) b.po_state.vs_allocas births = births`
    by suspend "births" >>
  `ptr_paired_prefix R lp positions lo vs0 C Ct
      (h ++ [b]) b (ht ++ [bt]) bt (done ++ [LENGTH h - 1])
      (LENGTH h :: tokens) (registry |+ (LENGTH h,f)) births
      (MAP (op_prov TG) ops) FEMPTY ((PT,TG)::saved)
      (entries |+ (LENGTH h,LENGTH ht))
      (H ++ [(LENGTH h :: tokens,registry |+ (LENGTH h,f),births,
        MAP (op_prov TG) ops,FEMPTY,((PT,TG)::saved),
        entries |+ (LENGTH h,LENGTH ht))])
      ((LENGTH h - 1,LENGTH ht - 1)::calls) ws` by suspend "prefix" >>
  `fn_inst_wf b.po_fn` by simp[Abbr `b`, ptr_observe_def] >>
  drule_all ptr_paired_prefix_normalize >> strip_tac >>
  qexistsl_tac [`f`,`args`,`cs`,`cs'`,`i`,`b`,`births`,`bb`,`n`,`delta`,`snapshots`] >>
  simp[Abbr `b`, ptr_observe_def]
QED

Resume ptr_paired_invoke_prefix_normalize[tagged]:
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_chrono_history_reachable >> strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (fs[ptr_observation_reachable_def] >>
     qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >> gvs[]) >>
  `decode_invoke a.po_inst = SOME (nm,ops)` by
    (gvs[concretize_positions_unchanged]) >>
  `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state = a` by
    simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
  `ptr_tagged_chrono_step C (HD tokens)
    (ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
      a.po_fn a.po_inst a.po_state) b PT TG saved
      (MAP (op_prov TG) ops) FEMPTY ((PT,TG)::saved)` by
    (simp[NoAsms, Abbr `b`] >> irule (cj 3 ptr_tagged_chrono_step_rules) >>
     metis_tac[]) >>
  metis_tac[]
QED
Resume ptr_paired_invoke_prefix_normalize[births]:
  `first_block_no_phi f` by
    (fs[EVERY_MEM] >> metis_tac[venomInstTheory.lookup_function_MEM]) >>
  `cs' = cs` by metis_tac[ptr_setup_no_phi_entry] >>
  gvs[Abbr `b`, ptr_observe_def, setup_callee_def, AllCaseEqs(),
    ptr_birth_overlay_def, ptr_birth_lift_def, FUNION_FEMPTY_1]
QED
Resume ptr_paired_invoke_prefix_normalize[prefix]:
  `b.po_fn = f /\ bt.po_fn = g /\
   LENGTH b.po_stack = SUC (LENGTH a.po_stack) /\
   LENGTH bt.po_stack = SUC (LENGTH at.po_stack)` by
    gvs[Abbr `b`, ptr_observe_def] >>
  qpat_x_assum `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ptr_paired_prefix_def]) >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  rewrite_tac[ptr_paired_prefix_def] >>
  conj_tac >- suspend "transcript" >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "samples" >>
  conj_tac >- suspend "alignment" >>
  conj_tac >- suspend "callers" >>
  suspend "writes"
QED
Resume ptr_paired_invoke_prefix_normalize[transcript]:
  `a.po_inst.inst_id = at.po_inst.inst_id` by
    simp[concretize_positions_inst_id] >>
  `R b.po_fn bt.po_fn` by fs[ptr_paired_code_def] >>
  drule (cj 3 ptr_structural_transcript_rules) >>
  disch_then drule >> disch_then drule >>
  simp[ptr_activation_tokens_def, ptr_activation_registry_def]
QED
Resume ptr_paired_invoke_prefix_normalize[samples]:
  irule ptr_paired_samples_pair >> simp[ptr_paired_sample_def] >>
  gvs[Abbr `b`, ptr_observe_def] >>
  fs[ptr_mixed_vars_def, entry_taint_def, op_taint_def]
QED
Resume ptr_paired_invoke_prefix_normalize[alignment]:
  irule ptr_paired_alignment_pair >> simp[] >>
  conj_tac
  >- (gvs[Abbr `b`, ptr_observe_def, ptr_paired_cursor_def] >>
      qexists_tac `indices` >> simp[]) >>
  gvs[Abbr `b`, ptr_observe_def, ptr_paired_params_def] >>
  drule ptr_args_transport_lengths >> strip_tac >> gvs[]
QED
Resume ptr_paired_invoke_prefix_normalize[callers]:
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  `EL (LENGTH h - 1) h = a /\ EL (LENGTH ht - 1) ht = at /\
   EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (`H <> []` by (Cases_on `H` >> gvs[]) >>
     gvs[LAST_EL, PRE_SUB1]) >>
  `at.po_inst.inst_opcode = INVOKE` by simp[concretize_positions_unchanged] >>
  fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  rewrite_tac[ptr_paired_callers_def] >>
  fs[ptr_paired_callers_def] >> simp[ptr_observe_def] >>
  gen_tac >> strip_tac >> Cases_on `k`
  >- (gvs[Abbr `b`, ptr_observe_def, ptr_paired_call_def,
       ptr_paired_frame_def, ptr_paired_saved_tags_def, EL_APPEND_EQN]) >>
  rename1 `SUC k < _` >>
  `k < LENGTH calls` by simp[] >>
  qpat_x_assum `!k. k < LENGTH calls ==> _` drule >> strip_tac >>
  gvs[Abbr `b`, ptr_observe_def] >>
  Cases_on `EL k calls` >>
  irule ptr_paired_call_retained >>
  goal_assum (drule_at Any) >> gvs[ptr_paired_call_def, EVERY_EL]
QED
Resume ptr_paired_invoke_prefix_normalize[writes]:
  `EVERY (\n. SUC n < LENGTH h) done` by
    (drule ptr_structural_trace_embedding >>
     simp[ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN] >> decide_tac) >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  irule (SRULE [] (Q.SPECL [`ws`,`[]`] ptr_paired_writes_pair)) >>
  gvs[ptr_paired_samples_def, ptr_sample_list_def]
QED
Finalise ptr_paired_invoke_prefix_normalize
