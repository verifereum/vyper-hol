Theory gasFocusConcretizeCutAlloca
Ancestors concretizePtrOrdinaryNext concretizePtrMixedAllocationTransport
  concretizePtrAllocationSize concretizePtrActivationBirths
  concretizePtrExecutedCoverage concretizeStepRetpc venomWfProps
  passSharedDefs concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStagePlacements contextCodegenRel unitLabelMapIdentity
  venomInst venomWf cfgWf unitShapeDefs o1PassContract list
  concretizeMemLocDefs concretizePtrChronologicalHistory venomExecSemantics
  venomState ptrDiscipline concretizePtrRequestHistory
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrEventEmbedding concretizePtrActivationChronology
  concretizePtrAllocationTransport codegenRel concretizePtrSourceOwnership
  concretizePtrDeletedGapHistory concretizePtrLedgerProbe concretizePtrOpaqueRetpc
  concretizeStepStructure

(* ALLOCA operands and placement come from the actual source fetch, not
   from a whole-run pointer discipline for the initial state. *)
Theorem ptr_focus_alloca_inputs[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state /\
  active_inst a.po_fn a.po_inst a.po_state /\
  a.po_inst.inst_opcode = ALLOCA /\
  fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn ==>
  ?sz out pos.
    a.po_inst.inst_operands = [Lit sz] /\
    a.po_inst.inst_outputs = [out] /\ ~retpc_var a.po_fn out /\
    FLOOKUP (lp a.po_fn) (Allocation a.po_inst.inst_id) = SOME pos /\
    FLOOKUP positions (Allocation a.po_inst.inst_id) = SOME (pos,w2n sz) /\
    (!base size. FLOOKUP a.po_state.vs_allocas a.po_inst.inst_id = SOME (base,size)
      ==> size = w2n sz)
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_placements >> strip_tac >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes_static >> simp[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (gvs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `inst_wf a.po_inst` by
    (fs[fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  qpat_x_assum `inst_wf a.po_inst` mp_tac >> simp[inst_wf_def] >> strip_tac >>
  `?out. a.po_inst.inst_outputs = [out]` by
    (Cases_on `a.po_inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  `~retpc_var a.po_fn out` by
    (strip_tac >> qpat_x_assum `retpc_shape_ok _` mp_tac >>
     pure_rewrite_tac[retpc_shape_ok_def] >> disch_then (mp_tac o cj 3) >>
     disch_then (qspecl_then [`a.po_inst`,`out`] mp_tac) >> simp[]) >>
  `fn_inst_ids_distinct a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `get_alloca_size a.po_fn (Allocation a.po_inst.inst_id) = w2n sz` by
    (irule ptr_alloca_inst_size >> simp[]) >>
  drule_all ptr_stage_alloca_mems >> strip_tac >>
  `FLOOKUP positions (Allocation a.po_inst.inst_id) = SOME (p,w2n sz)` by
    (fs[ptr_stage_placements_def] >> metis_tac[lookup_function_MEM]) >>
  `FLOOKUP (lp a.po_fn) (Allocation a.po_inst.inst_id) = SOME p` by
    (qpat_x_assum `ptr_paired_code _ _ _ _ _` mp_tac >>
     qpat_x_assum `MEM a.po_inst (fn_insts _)` mp_tac >>
     simp[ptr_paired_code_def, fn_insts_MEM] >> rpt strip_tac >>
     first_x_assum (qspecl_then [`bb`,`a.po_inst`] mp_tac) >> simp[]) >>
  qexistsl_tac [`sz`,`out`,`p`] >> simp[] >>
  rpt strip_tac >> drule_all ptr_frame_current_allocation_size_static >> simp[]
QED

Theorem ptr_focus_alloca_target[local]:
  a.po_inst.inst_opcode = ALLOCA /\ a.po_inst.inst_outputs = [out] /\
  FLOOKUP (lp a.po_fn) (Allocation a.po_inst.inst_id) = SOME pos /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  step_inst 0 C' at.po_inst at.po_state =
    OK (update_var (HD a.po_inst.inst_outputs) (n2w pos) at.po_state) /\
  zt.po_state = (update_var (HD a.po_inst.inst_outputs) (n2w pos) at.po_state
                 with vs_inst_idx := SUC at.po_state.vs_inst_idx) /\
  zt.po_fn = at.po_fn /\ zt.po_stack = at.po_stack /\
  active_inst zt.po_fn zt.po_inst zt.po_state
Proof
  strip_tac >>
  `at.po_inst.inst_opcode = ASSIGN /\
   at.po_inst.inst_operands = [Lit (n2w pos)] /\
   at.po_inst.inst_outputs = [HD a.po_inst.inst_outputs]` by
    simp[concretize_inst_with_positions_def, mk_assign_inst_def] >>
  qpat_x_assum `at.po_inst = concretize_inst_with_positions _ _` kall_tac >>
  `!fuel. step_inst fuel C' at.po_inst at.po_state =
     OK (update_var (HD a.po_inst.inst_outputs) (n2w pos) at.po_state)` by
    (simp[step_inst_non_invoke] >> pure_once_rewrite_tac[step_inst_base_def] >>
     pure_asm_rewrite_tac[] >> simp[eval_operand_def]) >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def]
QED

Theorem ptr_focus_alloca_source_fields[local]:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
  inst.inst_outputs = [out] /\ step_inst 0 C inst s = OK u ==>
  u.vs_prev_bb = s.vs_prev_bb /\ u.vs_params = s.vs_params /\
  !tn t out' val.
    ptr_history_content tn s t ==>
    ptr_history_content (step_taint inst s u tn) u (update_var out' val t)
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >> pure_once_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[] >> simp[exec_alloca_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> rpt strip_tac >>
  irule ptr_history_content_masks >> qexists `tn` >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       GSYM update_var_def]
QED

Theorem ptr_focus_alloca_attach[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved /\
  b.po_fn = a.po_fn /\ zt.po_fn = at.po_fn /\
  b.po_stack = a.po_stack /\ zt.po_stack = at.po_stack /\
  B = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births /\
  (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP B owner = SOME site) /\
  b.po_state.vs_params = a.po_state.vs_params /\
  zt.po_state.vs_params = at.po_state.vs_params /\
  a.po_inst.inst_opcode = ALLOCA /\ a.po_inst.inst_id = at.po_inst.inst_id /\
  ptr_chrono_step C' at zt /\ ptr_paired_cursor lp b zt /\
  ptr_paired_sample positions b zt (tokens,registry,B,PT,TG',saved,entries) ==>
  ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [b]) b (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry B PT TG' saved entries
    (H ++ [(tokens,registry,B,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  `ptr_paired_params positions b zt (tokens,registry,B,PT,TG',saved,entries)` by
    (fs[ptr_paired_params_def] >> metis_tac[ptr_args_transport_birth_extension]) >>
  `ptr_structural_transcript R vs C C' (h ++ [b]) b (ht ++ [zt]) zt
    (done ++ [LENGTH h - 1]) tokens registry B PT TG' saved entries
    (H ++ [(tokens,registry,B,PT,TG',saved,entries)])` by
    (drule (cj 3 ptr_structural_transcript_rules) >> disch_then drule >>
     disch_then drule >> simp[ptr_activation_tokens_def, ptr_activation_registry_def]) >>
  `LAST h = a /\ EVERY (\n. SUC n < LENGTH h) done` by
    (conj_tac
     >- (drule ptr_paired_prefix_transcript >>
         disch_then (strip_assume_tac o MATCH_MP ptr_structural_transcript_erasure) >>
         drule ptr_structural_trace_source >> metis_tac[ptr_chrono_history_end]) >>
     qpat_assum `ptr_structural_transcript _ _ _ _ (h ++ _) _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP ptr_structural_transcript_erasure) >>
     drule ptr_structural_trace_embedding >>
     simp[ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN] >> decide_tac) >>
  gvs[ptr_paired_prefix_def] >>
  conj_tac >- (irule ptr_paired_samples_pair >> simp[]) >>
  conj_tac >- (irule ptr_paired_alignment_pair >> simp[]) >>
  conj_tac >- (irule ptr_paired_callers_retained >> simp[] >>
               fs[ptr_paired_samples_def, ptr_sample_list_def] >> qexistsl [`LAST h`,`at`] >> simp[]) >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM APPEND_NIL))) >>
  irule ptr_paired_writes_pair >>
  simp[step_writes_def, source_memory_write_ranges_def, fixed_source_write_range_def,
       range_bytes_def] >> fs[ptr_paired_samples_def, ptr_sample_list_def]
QED

Theorem ptr_focus_alloca_step:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = ALLOCA /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?b B TG'.
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [b]) b (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry B PT TG' saved entries
      (H ++ [(tokens,registry,B,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes_static >> simp[]) >>
  `fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
   EVERY bb_well_formed a.po_fn.fn_blocks /\ ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, wf_function_def,
        EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_focus_alloca_inputs >> strip_tac >>
  drule_all ptr_focus_alloca_target >> strip_tac >>
  fs[ptr_paired_sample_def] >>
  drule_all ptr_mixed_alloca_transport >>
  disch_then (qspecl_then [`HD tokens`,`0`,`PT`,`C'`,`C`] strip_assume_tac) >>
  rename1 `step_inst 0 C a.po_inst a.po_state = OK post` >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
   a.po_inst.inst_opcode <> NOP` by simp[is_terminator_def] >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (irule ptr_ordinary_next_active >> simp[] >> qexists `a.po_inst` >> simp[]) >>
  qabbrev_tac `b = ptr_ledger_next a i post` >>
  qabbrev_tac `B = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births` >>
  qabbrev_tac `TG' = ptr_tagged_step (HD tokens) PT TG a.po_inst post` >>
  `b.po_state = (post with vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
   b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_inst = i` by
    simp[Abbr `b`, ptr_ledger_next_def, ptr_observe_def] >>
  `ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved` by
    suspend "tagged" >>
  `!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP B owner = SOME site` by
    suspend "births" >>
  `ptr_paired_cursor lp b zt` by suspend "cursor" >>
  `ptr_paired_sample positions b zt (tokens,registry,B,PT,TG',saved,entries)` by
    suspend "sample" >>
  qexistsl [`b`,`B`,`TG'`] >> irule ptr_focus_alloca_attach >> suspend "attach"
QED

Resume ptr_focus_alloca_step[tagged]:
  simp[Abbr `b`, Abbr `TG'`, ptr_ledger_next_def] >>
  `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state = a` by
    simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
  drule_all (cj 1 ptr_tagged_chrono_step_rules) >> simp[] >> metis_tac[]
QED

Resume ptr_focus_alloca_step[births]:
  `ptr_source_birth_caches vs C h a tokens registry births` by
    metis_tac[ptr_source_ownership_caches] >>
  `ptr_chrono_step C a b` by metis_tac[ptr_tagged_chrono_step_projection] >>
  drule ptr_source_birth_caches_snoc_retained >>
  disch_then (qspec_then `b` mp_tac) >>
  simp[Abbr `B`, ptr_activation_tokens_def]
QED

Resume ptr_focus_alloca_step[cursor]:
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  `!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP (lp a.po_fn) (Allocation ai.inst_id) = SOME p` by
    (rpt strip_tac >> drule_all ptr_paired_stage_local_allocas >> simp[]) >>
  drule_all (cj 1 ptr_focus_alloca_source_fields) >> strip_tac >>
  drule ptr_ordinary_next_cursor >> disch_then irule >> simp[update_var_def]
QED

Resume ptr_focus_alloca_step[sample]:
  simp[ptr_paired_sample_def] >>
  conj_tac
  >- (`!base size. FLOOKUP post.vs_allocas a.po_inst.inst_id = SOME (base,size) ==>
          FLOOKUP B (HD tokens,a.po_inst.inst_id) = SOME (base,size)` by
        simp[Abbr `B`, ptr_birth_overlay_lookup] >>
      `step_inst 0 C' (concretize_inst_with_positions (lp a.po_fn) a.po_inst) at.po_state =
         OK (update_var (HD a.po_inst.inst_outputs) (n2w pos) at.po_state)` by
        (qpat_assum `at.po_inst = concretize_inst_with_positions _ _`
           (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
      `ptr_mixed_vars B positions TG' (step_taint a.po_inst a.po_state post a.po_taint)
         a.po_fn at.po_fn post (update_var (HD a.po_inst.inst_outputs) (n2w pos) at.po_state)` by
        (qpat_assum `!births' t'. _ ==> ptr_mixed_vars _ _ _ _ _ _ _ _`
           (qspecl_then [`B`,`update_var (HD a.po_inst.inst_outputs) (n2w pos) at.po_state`] mp_tac) >>
         simp[]) >>
      irule ptr_mixed_vars_fields >> goal_assum (drule_at Any) >>
      simp[Abbr `b`, ptr_ledger_next_def, ptr_observe_def]) >>
  drule_all ptr_focus_alloca_source_fields >> strip_tac >>
  simp[Abbr `b`, ptr_ledger_next_def, ptr_observe_def] >>
  first_x_assum irule >> simp[]
QED

Resume ptr_focus_alloca_step[attach]:
  drule_all ptr_focus_alloca_source_fields >> strip_tac >>
  simp[] >> qexistsl [`TG`,`a`,`at`,`births`] >>
  simp[Abbr `B`, update_var_def, concretize_inst_with_positions_def, mk_assign_inst_def]
QED
Finalise ptr_focus_alloca_step
