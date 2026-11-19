(* Structural INVOKE transport from current operand restrictions.
 * The discipline-based public entry points remain compatibility corollaries.
 *)
Theory concretizePtrPairedCallRestricted
Ancestors passTransform
  concretizePtrPairedEntry concretizePtrPairedFields concretizePtrValueSelection
  o1PassLift analysisSimProofsBase unitShapeDefs passSimulationProps
  passSharedDefs passSimulationDefs
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizePtrSourceOwnership
  concretizePtrOpaqueRetpc concretizePtrSharedFields concretizePtrValueTransport
  concretizePtrRequestHistory
  concretizeStepStructure concretizeStepShape
  concretizeStepRetpc concretizeStageShape concretizeStepContract
  contextCodegenRel unitLabelMapIdentity venomInst o1PassContract
  ptrDiscipline venomExecSemantics venomExecProofs venomWf venomState list finite_map
  concretizePtrPairedPrefixProbe concretizePtrActivationBirths
  concretizePtrActivationChronology concretizePtrEventEmbedding rich_list arithmetic

Theorem ptr_paired_invoke_args_restricted:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  EVERY (ptr_nonopaque_operand a.po_fn) ops /\
  MAP (op_taint a.po_taint) ops = REPLICATE (LENGTH ops) {} /\
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
  simp[] >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
    a.po_state at.po_state` by fs[ptr_paired_sample_def] >>
  drule_all ptr_mixed_vars_eval_operands >>
  Cases_on `eval_operands ops a.po_state` >> simp[] >>
  strip_tac >> drule ptr_args_transport_lengths >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem ptr_setup_no_phi_entry_core:
  first_block_no_phi f /\ setup_callee f args s = SOME cs ==>
  enters_block f cs cs /\ (!u. enters_block f cs u ==> u = cs)
Proof
  simp[setup_callee_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  `lookup_block (HD f.fn_blocks).bb_label f.fn_blocks = SOME (HD f.fn_blocks)` by
    (Cases_on `f.fn_blocks` >> gvs[lookup_block_def, FIND_def, INDEX_FIND_def]) >>
  fs[first_block_no_phi_def] >>
  simp[enters_block_def, eval_phis_no_phis, no_phis_phi_prefix_length_zero]
QED

Theorem ptr_paired_invoke_entry_restricted:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  EVERY (ptr_nonopaque_operand a.po_fn) ops /\
  MAP (op_taint a.po_taint) ops = REPLICATE (LENGTH ops) {} /\
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
  setup_callee g argst at.po_state = SOME ct /\ enters_block g ct ct' /\
  active_inst g it ct' ==>
  ?f args cs cs' i.
    lookup_function nm C.ctx_functions = SOME f /\
    ptr_paired_code R lp positions f g /\
    eval_operands ops a.po_state = SOME args /\
    ptr_args_transport births positions (MAP (op_prov TG) ops)
      (REPLICATE (LENGTH args) {}) args argst /\
    setup_callee f args a.po_state = SOME cs /\ enters_block f cs cs' /\
    active_inst f i cs' /\ ptr_history_content (a.po_taint with t_var := FEMPTY) cs' ct' /\
    ptr_mixed_vars births positions FEMPTY entry_taint f g cs' ct' /\
    ptr_args_transport births positions (MAP (op_prov TG) ops)
      (REPLICATE (LENGTH args) {}) cs'.vs_params ct'.vs_params /\
    ptr_paired_cursor lp
      (a with <|po_fn := f; po_inst := i; po_state := cs'|>)
      (at with <|po_fn := g; po_inst := it; po_state := ct'|>)
Proof
  strip_tac >> drule_all ptr_paired_invoke_args_restricted >> strip_tac >>
  `?f. lookup_function nm C.ctx_functions = SOME f /\
    ptr_paired_code R lp positions f g` by
    (drule_all list_rel_lookup_function >> disch_then (qspec_then `nm` mp_tac) >>
     Cases_on `lookup_function nm C.ctx_functions` >> simp[]) >>
  `MEM f C.ctx_functions /\ MEM g Ct.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  `first_block_no_phi f /\ fn_inst_wf f /\
    EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
    (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation inst.inst_id))) /\
    ALL_DISTINCT (fn_labels g)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `NULL f.fn_blocks = NULL g.fn_blocks /\
    (HD f.fn_blocks).bb_label = (HD g.fn_blocks).bb_label` by
    (fs[ptr_paired_code_def, concretize_positions_blocks] >>
     Cases_on `f.fn_blocks` >> simp[concretize_positions_block_label]) >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `ptr_history_content a.po_taint a.po_state at.po_state` by fs[ptr_paired_sample_def] >>
  drule_all ptr_history_content_setup >>
  disch_then (qspec_then `args` strip_assume_tac) >>
  `~NULL f.fn_blocks` by
    (fs[setup_callee_def, AllCaseEqs()]) >>
  `first_block_no_phi g` by
    (qpat_x_assum `ptr_paired_code R lp positions f g` mp_tac >>
     simp[ptr_paired_code_def] >> strip_tac >>
     gvs[first_block_no_phi_def, concretize_positions_blocks] >>
     Cases_on `f.fn_blocks` >>
     gvs[clear_nops_block_def, block_map_transform_def,
         EVERY_FILTER, EVERY_MAP, EVERY_MEM, MEM_FILTER, MEM_MAP] >>
     metis_tac[concretize_positions_phi]) >>
  `enters_block f cs cs /\ ct' = ct` by
    metis_tac[ptr_setup_no_phi_entry_core] >>
  gvs[] >>
  `ptr_mixed_vars births positions FEMPTY entry_taint f g cs ct` by
    (irule ptr_mixed_vars_setup >> simp[] >>
     conj_tac
     >- (fs[ptr_paired_code_def, retpc_var_def] >>
         qpat_assum `g.fn_blocks = _`
           (mp_then Any mp_tac concretize_blocks_copy_phi) >>
         simp[concretize_positions_copy_phi]) >>
     metis_tac[]) >>
  `ptr_args_transport births positions (MAP (op_prov TG) ops)
    (REPLICATE (LENGTH args) {}) cs.vs_params ct.vs_params` by
    (`NULL f.fn_blocks = NULL g.fn_blocks` by simp[] >>
     drule_all ptr_setup_callee_transport >> metis_tac[]) >>
  `cs.vs_current_bb = ct.vs_current_bb /\ cs.vs_prev_bb = ct.vs_prev_bb` by
    (qpat_x_assum `setup_callee f _ _ = _` mp_tac >>
     qpat_x_assum `setup_callee g _ _ = _` mp_tac >>
     simp[setup_callee_def] >> rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `?i. active_inst f i cs /\ ptr_paired_cursor lp
    (a with <|po_fn := f; po_inst := i; po_state := cs|>)
    (at with <|po_fn := g; po_inst := it; po_state := ct|>)` by
    (mp_tac (ptr_paired_entry_cursor |> SPEC_ALL |>
       INST_TYPE [alpha |-> ``:num``] |>
       Q.INST [`a` |-> `a with <|po_fn := f; po_state := cs|>`,
               `at` |-> `at with <|po_fn := g; po_inst := it; po_state := ct|>`] |>
       GEN_ALL) >>
     simp[] >> disch_then irule >> metis_tac[]) >>
  qexistsl_tac [`cs`,`i`] >> simp[]
QED

Theorem ptr_paired_invoke_prefix_normalize_restricted:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  EVERY (ptr_nonopaque_operand a.po_fn) ops /\
  MAP (op_taint a.po_taint) ops = REPLICATE (LENGTH ops) {} /\
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
  strip_tac >> drule_all ptr_paired_invoke_entry_restricted >> strip_tac >>
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

Resume ptr_paired_invoke_prefix_normalize_restricted[tagged]:
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
Resume ptr_paired_invoke_prefix_normalize_restricted[births]:
  `first_block_no_phi f` by
    (fs[EVERY_MEM] >> metis_tac[venomInstTheory.lookup_function_MEM]) >>
  `cs' = cs` by metis_tac[ptr_setup_no_phi_entry_core] >>
  gvs[Abbr `b`, ptr_observe_def, setup_callee_def, AllCaseEqs(),
    ptr_birth_overlay_def, ptr_birth_lift_def, FUNION_FEMPTY_1]
QED
Resume ptr_paired_invoke_prefix_normalize_restricted[prefix]:
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
Resume ptr_paired_invoke_prefix_normalize_restricted[transcript]:
  `a.po_inst.inst_id = at.po_inst.inst_id` by
    simp[concretize_positions_inst_id] >>
  `R b.po_fn bt.po_fn` by fs[ptr_paired_code_def] >>
  drule (cj 3 ptr_structural_transcript_rules) >>
  disch_then drule >> disch_then drule >>
  simp[ptr_activation_tokens_def, ptr_activation_registry_def]
QED
Resume ptr_paired_invoke_prefix_normalize_restricted[samples]:
  irule ptr_paired_samples_pair >> simp[ptr_paired_sample_def] >>
  gvs[Abbr `b`, ptr_observe_def] >>
  fs[ptr_mixed_vars_def, entry_taint_def, op_taint_def]
QED
Resume ptr_paired_invoke_prefix_normalize_restricted[alignment]:
  irule ptr_paired_alignment_pair >> simp[] >>
  conj_tac
  >- (gvs[Abbr `b`, ptr_observe_def, ptr_paired_cursor_def] >>
      qexists_tac `indices` >> simp[]) >>
  gvs[Abbr `b`, ptr_observe_def, ptr_paired_params_def] >>
  drule ptr_args_transport_lengths >> strip_tac >> gvs[]
QED
Resume ptr_paired_invoke_prefix_normalize_restricted[callers]:
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
Resume ptr_paired_invoke_prefix_normalize_restricted[writes]:
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
Finalise ptr_paired_invoke_prefix_normalize_restricted
