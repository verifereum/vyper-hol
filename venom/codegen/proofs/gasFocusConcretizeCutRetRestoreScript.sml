Theory gasFocusConcretizeCutRetRestore
Ancestors concretizePtrReturnProduction[qualified]
  concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrReturnTransport concretizePtrOpaqueRetpc
  concretizePtrChronologicalHistory concretizePtrStructuralTranscript
  concretizePtrSourceOwnership concretizePtrStructuralTrace
  concretizePtrHistoricalPlacement concretizePtrOperationalOpcodes
  concretizePtrRequestHistory ptrDisciplineCallCtx contextCodegenRel venomExecSemantics venomState venomInst
  venomExecProofs venomInstProofs1
  finite_map list rich_list arithmetic pred_set pair

(* The saved tags and the two caller states must come from the same
   completed INVOKE, not from the current callee sample. *)
Theorem focus_ret_saved_head[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_stack <> [] ==>
  ?r ts rg B PTc TGc sv en.
    r < LENGTH done /\ r < LENGTH ht /\ EL r done < LENGTH h /\
    at.po_stack <> [] /\ saved <> [] /\ HD saved = (PTc,TGc) /\
    ptr_paired_frame (HD a.po_stack) (EL (EL r done) h) /\
    ptr_paired_frame (HD at.po_stack) (EL r ht) /\
    (EL (EL r done) h).po_inst.inst_opcode = INVOKE /\
    ptr_paired_cursor lp (EL (EL r done) h) (EL r ht) /\
    EL (EL r done) H = (ts,rg,B,PTc,TGc,sv,en) /\
    ptr_mixed_vars B positions TGc (EL (EL r done) h).po_taint
      (EL (EL r done) h).po_fn (EL r ht).po_fn
      (EL (EL r done) h).po_state (EL r ht).po_state /\
    ptr_history_content (EL (EL r done) h).po_taint
      (EL (EL r done) h).po_state (EL r ht).po_state
Proof
  strip_tac >>
  drule ptr_paired_prefix_callers >> simp[ptr_paired_callers_def] >> strip_tac >>
  `0 < LENGTH calls /\ at.po_stack <> [] /\ saved <> []` by
    (Cases_on `calls` >> Cases_on `a.po_stack` >>
     Cases_on `at.po_stack` >> Cases_on `saved` >> gvs[]) >>
  qpat_x_assum `!k. k < LENGTH calls ==> _` (qspec_then `0` mp_tac) >> simp[] >>
  Cases_on `HD calls` >> simp[ptr_paired_call_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_paired_saved_tags _ snap` >>
  PairCases_on `snap` >> fs[ptr_paired_saved_tags_def] >>
  rename1 `r < LENGTH done` >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `r < LENGTH ht /\ EL r done < LENGTH h` by
    (fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_MEM] >>
     metis_tac[EL_MEM]) >>
  drule (cj 2 ptr_paired_prefix_alignment) >>
  disch_then (qspec_then `r` mp_tac) >> simp[EL_APPEND_EQN] >> strip_tac >>
  drule ptr_paired_samples_history >> disch_then (qspec_then `r` mp_tac) >>
  simp[EL_APPEND_EQN] >> strip_tac >>
  qpat_x_assum `q = EL r done` SUBST_ALL_TAC >>
  fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  qpat_x_assum `!j. j < LENGTH ht ==> ptr_paired_sample _ _ _ _`
    (qspec_then `r` mp_tac) >>
  simp[EL_APPEND_EQN, ptr_paired_sample_def] >> strip_tac >>
  qexists `r` >> simp[] >> metis_tac[]
QED

Theorem focus_ret_target_resume[local]:
  at.po_inst.inst_opcode = RET /\
  at.po_stack <> [] /\
  step_inst 0 C' at.po_inst at.po_state = IntRet ret at.po_state /\
  bind_outputs (HD at.po_stack).cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state (HD at.po_stack).cf_state at.po_state)) = SOME tr /\
  ptr_chrono_step C' at zt ==>
  zt.po_fn = (HD at.po_stack).cf_fn /\ zt.po_stack = TL at.po_stack /\
  zt.po_state = (tr with vs_inst_idx := SUC (HD at.po_stack).cf_state.vs_inst_idx) /\
  active_inst zt.po_fn zt.po_inst zt.po_state
Proof
  strip_tac >>
  `!i s fuel. i.inst_opcode = RET ==>
      step_inst fuel C' i s = step_inst 0 C' i s` by
    (rpt strip_tac >> irule ptrSafeRunTheory.step_inst_non_invoke_fuel >> simp[]) >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases, ptr_observe_def] >>
  rpt strip_tac >> gvs[is_terminator_def]
QED

Theorem focus_ret_bind_control[local]:
  bind_outputs os vals s = SOME t ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_prev_bb = s.vs_prev_bb
Proof
  strip_tac >>
  drule (Q.ISPEC `(\u. (u.vs_current_bb,u.vs_prev_bb))` bind_outputs_preserves
    |> SIMP_RULE (srw_ss()) [update_var_def]) >> simp[]
QED

Theorem focus_ret_observation_stack[local]:
  ptr_observation_reachable vs C a /\ a.po_stack <> [] ==>
  MEM (HD a.po_stack).cf_fn C.ctx_functions /\
  a.po_state.vs_call_ctx.cc_address = (HD a.po_stack).cf_state.vs_call_ctx.cc_address
Proof
  strip_tac >> fs[ptr_observation_reachable_def] >>
  drule ptr_frame_context_membership >>
  drule ptr_reachable_stack_call_ctx >>
  disch_then (qspec_then `HD a.po_stack` mp_tac) >>
  Cases_on `a.po_stack` >> gvs[]
QED

Theorem focus_ret_saved_births[local]:
  ptr_structural_transcript R vs C C' h a ht at done tokens registry births PT TG saved entries H /\
  i < LENGTH h /\ EL i H = (ts,rg,B,PTc,TGc,sv,en) ==>
  !key site. FLOOKUP B key = SOME site ==> FLOOKUP births key = SOME site
Proof
  strip_tac >> drule ptr_structural_transcript_endpoint >> strip_tac >>
  `EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (Cases_on `H` >> gvs[LAST_EL, arithmeticTheory.PRE_SUB1]) >>
  rpt strip_tac >>
  `i <= LENGTH h - 1 /\ LENGTH h - 1 < LENGTH h` by decide_tac >>
  drule_all (Q.SPEC `LENGTH h - 1` ptr_transcript_birth_retained) >> simp[]
QED

Theorem focus_ret_pop_tagged[local]:
  a.po_stack <> [] /\ saved <> [] /\ HD saved = (PTc,TGc) /\
  active_inst a.po_fn a.po_inst a.po_state /\
  step_inst 0 C a.po_inst a.po_state = IntRet ret a.po_state /\
  bind_outputs (HD a.po_stack).cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state (HD a.po_stack).cf_state a.po_state)) = SOME sr /\
  active_inst (HD a.po_stack).cf_fn i
    (sr with vs_inst_idx := SUC (HD a.po_stack).cf_state.vs_inst_idx) ==>
  ptr_tagged_chrono_step C token a
    (ptr_observe (TL a.po_stack) (HD a.po_stack).cf_params
      (DRESTRICT (HD a.po_stack).cf_prov (COMPL (set (HD a.po_stack).cf_inst.inst_outputs)))
      (a.po_taint with t_var := DRESTRICT (HD a.po_stack).cf_tvar
        (COMPL (set (HD a.po_stack).cf_inst.inst_outputs)))
      (HD a.po_stack).cf_fn i
      (sr with vs_inst_idx := SUC (HD a.po_stack).cf_state.vs_inst_idx))
    PT TG saved PTc (DRESTRICT TGc (COMPL (set (HD a.po_stack).cf_inst.inst_outputs))) (TL saved)
Proof
  strip_tac >>
  `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state = a` by
    simp[ptr_observe_def, ptr_observation_component_equality] >>
  pop_assum (fn th => SUBST_OCCS_TAC [([1], SYM th)]) >>
  Cases_on `a.po_stack` >> gvs[] >> Cases_on `saved` >> gvs[] >>
  irule (cj 4 ptr_tagged_chrono_step_rules) >> simp[] >>
  qexistsl [`0`, `ret`, `a.po_state`] >> simp[]
QED

Theorem ptr_focus_ret_restore:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  EVERY (\f. retpc_shape_ok f /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  a.po_inst.inst_opcode = RET /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\
  step_inst 0 C a.po_inst a.po_state = IntRet ret a.po_state /\
  step_inst 0 C' at.po_inst at.po_state = IntRet ret at.po_state /\
  ret.iret_adopt_fmp = NONE /\
  a.po_stack <> [] /\ at.po_stack <> [] /\
  (HD a.po_stack).cf_inst.inst_outputs = (HD at.po_stack).cf_inst.inst_outputs /\
  bind_outputs (HD a.po_stack).cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state (HD a.po_stack).cf_state a.po_state)) = SOME sr /\
  bind_outputs (HD at.po_stack).cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state (HD at.po_stack).cf_state at.po_state)) = SOME tr ==>
  ?b PTc TGc outs B'.
    saved <> [] /\ HD saved = (PTc,TGc) /\ outs = (HD a.po_stack).cf_inst.inst_outputs /\
    b.po_state = (sr with vs_inst_idx := SUC (HD a.po_stack).cf_state.vs_inst_idx) /\
    b.po_stack = TL a.po_stack /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PTc
      (DRESTRICT TGc (COMPL (set outs))) (TL saved) /\
    ptr_history_content b.po_taint b.po_state zt.po_state /\ ptr_paired_cursor lp b zt /\
    ptr_mixed_vars B' positions (DRESTRICT TGc (COMPL (set outs)))
      b.po_taint b.po_fn zt.po_fn b.po_state zt.po_state /\
    B' = ptr_birth_overlay (HD (TL tokens)) b.po_state.vs_allocas births /\
    ptr_structural_transcript R vs C C'
      (h ++ [b]) b (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      (TL tokens) registry B' PTc (DRESTRICT TGc (COMPL (set outs)))
      (TL saved) entries
      (H ++ [(TL tokens,registry,B',PTc,DRESTRICT TGc (COMPL (set outs)),TL saved,entries)])
Proof
  strip_tac >> drule_all focus_ret_saved_head >> strip_tac >>
  `at.po_inst.inst_opcode = RET` by simp[concretizeStepStructureTheory.concretize_positions_unchanged] >>
  drule_all focus_ret_target_resume >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule_then (strip_assume_tac o MATCH_MP ptr_chrono_history_reachable) ptr_structural_trace_source >>
  drule_then (strip_assume_tac o MATCH_MP ptr_chrono_history_reachable) ptr_structural_trace_target >>
  `MEM (HD a.po_stack).cf_fn C.ctx_functions /\
   MEM (HD at.po_stack).cf_fn C'.ctx_functions /\
   a.po_state.vs_call_ctx.cc_address = (HD a.po_stack).cf_state.vs_call_ctx.cc_address /\
   at.po_state.vs_call_ctx.cc_address = (HD at.po_stack).cf_state.vs_call_ctx.cc_address` by
    metis_tac[focus_ret_observation_stack] >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state /\
   active_inst (EL (EL r done) h).po_fn (EL (EL r done) h).po_inst
     (EL (EL r done) h).po_state` by metis_tac[concretizePtrReturnProductionTheory.ptr_ret_cursor_active] >>
  qabbrev_tac `outs = (HD a.po_stack).cf_inst.inst_outputs` >>
  suspend "cursor"
QED

Resume ptr_focus_ret_restore[cursor]:
  `sr.vs_current_bb = (HD a.po_stack).cf_state.vs_current_bb /\
   tr.vs_current_bb = (HD at.po_stack).cf_state.vs_current_bb /\
   sr.vs_prev_bb = (HD a.po_stack).cf_state.vs_prev_bb /\
   tr.vs_prev_bb = (HD at.po_stack).cf_state.vs_prev_bb` by
    (imp_res_tac focus_ret_bind_control >> gvs[adopt_return_fmp_def, merge_callee_state_def]) >>
  `ALL_DISTINCT (fn_labels (EL r ht).po_fn) /\
   retpc_shape_ok (EL (EL r done) h).po_fn /\
   (!i. MEM i (fn_insts (EL (EL r done) h).po_fn) /\ i.inst_opcode = ALLOCA ==>
     ?p. FLOOKUP (lp (EL (EL r done) h).po_fn) (Allocation i.inst_id) = SOME p)` by
    (fs[ptr_paired_frame_def, EVERY_MEM, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  qabbrev_tac `b0 = ptr_observe (TL a.po_stack) (HD a.po_stack).cf_params
    (DRESTRICT (HD a.po_stack).cf_prov (COMPL (set outs)))
    (a.po_taint with t_var := DRESTRICT (HD a.po_stack).cf_tvar (COMPL (set outs)))
    (HD a.po_stack).cf_fn a.po_inst
    (sr with vs_inst_idx := SUC (HD a.po_stack).cf_state.vs_inst_idx)` >>
  `?i. active_inst b0.po_fn i b0.po_state /\
       ptr_paired_cursor lp (b0 with po_inst := i) zt` by
    (irule concretizePtrReturnProductionTheory.ptr_ret_caller_cursor >> conj_tac >- simp[] >>
     qexistsl [`EL (EL r done) h`, `EL r ht`] >>
     gvs[Abbr `b0`, ptr_observe_def, ptr_paired_frame_def]) >>
  qabbrev_tac `b = b0 with po_inst := i` >>
  `ptr_paired_cursor lp b zt` by fs[Abbr `b`] >>
  `b = ptr_observe (TL a.po_stack) (HD a.po_stack).cf_params
    (DRESTRICT (HD a.po_stack).cf_prov (COMPL (set outs)))
    (a.po_taint with t_var := DRESTRICT (HD a.po_stack).cf_tvar (COMPL (set outs)))
    (HD a.po_stack).cf_fn i
    (sr with vs_inst_idx := SUC (HD a.po_stack).cf_state.vs_inst_idx)` by
      simp[NoAsms, Abbr `b`, Abbr `b0`, ptr_observe_def] >>
  `ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PTc
     (DRESTRICT TGc (COMPL (set outs))) (TL saved)` by
    (qpat_x_assum `b = ptr_observe _ _ _ _ _ _ _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, Abbr `outs`] >> irule focus_ret_pop_tagged >>
     fs[Abbr `b0`, ptr_observe_def] >> metis_tac[]) >>
  suspend "restored_fields"
QED

Resume ptr_focus_ret_restore[restored_fields]:
  `!key site. FLOOKUP B key = SOME site ==> FLOOKUP births key = SOME site` by
    (rpt strip_tac >> irule focus_ret_saved_births >>
     goal_assum (drule_at (Pat `EL _ _ = (_,_,_,_,_,_,_)`)) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `ptr_mixed_vars births positions TGc (EL (EL r done) h).po_taint
     (EL (EL r done) h).po_fn (EL r ht).po_fn
     (EL (EL r done) h).po_state (EL r ht).po_state` by
    (irule ptr_mixed_vars_retained_births_tvar >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `MEM (EL (EL r done) h).po_inst (fn_insts (EL (EL r done) h).po_fn)` by
    (qpat_assum `active_inst (EL _ h).po_fn _ _` mp_tac >>
     simp[NoAsms, active_inst_def, unitLabelMapIdentityTheory.fn_insts_MEM] >>
     strip_tac >> goal_assum (drule_at Any) >>
     qpat_assum `EL _ bb.bb_instructions = _`
       (fn th => pure_once_rewrite_tac[GSYM th]) >> irule EL_MEM >> first_assum ACCEPT_TAC) >>
  `EVERY (\out. ~retpc_var (EL (EL r done) h).po_fn out) outs` by
    (simp[NoAsms, Abbr `outs`] >>
     qpat_assum `ptr_paired_frame (HD a.po_stack) _`
       (fn th => pure_rewrite_tac[CONJUNCT1 (CONJUNCT2 (REWRITE_RULE [ptr_paired_frame_def] th))]) >>
     irule ptr_retpc_invoke_outputs >> asm_rewrite_tac[]) >>
  `ptr_mixed_vars births positions (DRESTRICT TGc (COMPL (set outs)))
     ((EL (EL r done) h).po_taint with t_var :=
       DRESTRICT (EL (EL r done) h).po_taint.t_var (COMPL (set outs)))
     (HD a.po_stack).cf_fn (HD at.po_stack).cf_fn sr tr` by
    (gvs[ptr_paired_frame_def] >> irule (cj 2 ptr_mixed_return_bind) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `ptr_mixed_vars births positions (DRESTRICT TGc (COMPL (set outs)))
      b.po_taint b.po_fn zt.po_fn b.po_state zt.po_state` by
    (irule ptr_mixed_vars_fields >>
     gvs[ptr_paired_frame_def, ptr_observe_def] >>
     goal_assum (drule_at (Pat `ptr_mixed_vars _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `ptr_history_content a.po_taint a.po_state at.po_state` by fs[ptr_paired_sample_def] >>
  `ptr_taint_control
     ((HD a.po_stack).cf_state with vs_requests := (HD at.po_stack).cf_state.vs_requests)
     (HD at.po_stack).cf_state` by
    (fs[ptr_paired_frame_def] >> metis_tac[ptr_history_content_control]) >>
  `ptr_history_content b.po_taint b.po_state zt.po_state` by
    (simp[ptr_observe_def, Excl "ptr_history_content_cursor", Excl "ptr_history_content_tvar"] >>
     irule ptr_history_content_return >>
     rpt (goal_assum (drule_at Any)) >> gvs[]) >>
  suspend "transcript"
QED

Resume ptr_focus_ret_restore[transcript]:
  `LENGTH a.po_stack = SUC (LENGTH b.po_stack) /\
   LENGTH at.po_stack = SUC (LENGTH zt.po_stack)` by
    (Cases_on `a.po_stack` >> Cases_on `at.po_stack` >> gvs[ptr_observe_def]) >>
  `a.po_inst.inst_id = at.po_inst.inst_id` by
    (qpat_assum `at.po_inst = concretize_inst_with_positions _ _`
       (fn th => pure_once_rewrite_tac[th]) >>
     qpat_assum `a.po_inst.inst_opcode = RET` (fn th =>
       simp[NoAsms, th, concretizeMemLocDefsTheory.concretize_inst_with_positions_def])) >>
  qabbrev_tac `B' = ptr_birth_overlay (HD (TL tokens)) b.po_state.vs_allocas births` >>
  `ptr_structural_transcript R vs C C'
      (h ++ [b]) b (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      (TL tokens) registry B' PTc (DRESTRICT TGc (COMPL (set outs)))
      (TL saved) entries
      (H ++ [(TL tokens,registry,B',PTc,DRESTRICT TGc (COMPL (set outs)),TL saved,entries)])` by
    (simp[NoAsms, Abbr `B'`] >> drule ptr_structural_transcript_pair >>
     disch_then drule >> disch_then drule >>
     qpat_assum `LENGTH a.po_stack = SUC (LENGTH b.po_stack)` (fn th =>
       simp[NoAsms, th, concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
         concretizePtrActivationChronologyTheory.ptr_activation_registry_def]) >>
     disch_then irule >> asm_rewrite_tac[]) >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule ptr_tagged_chrono_step_projection >> strip_tac >>
  `!key site. FLOOKUP births key = SOME site ==> FLOOKUP B' key = SOME site` by
    (`ptr_activation_tokens h a b tokens = TL tokens` by
       (Cases_on `a.po_stack` >> gvs[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def]) >>
     drule concretizePtrActivationBirthsTheory.ptr_source_birth_caches_snoc_retained >>
     disch_then drule >>
     qpat_assum `ptr_activation_tokens h a b tokens = TL tokens`
       (fn th => simp[NoAsms, th, Abbr `B'`])) >>
  `ptr_mixed_vars B' positions (DRESTRICT TGc (COMPL (set outs)))
    b.po_taint b.po_fn zt.po_fn b.po_state zt.po_state` by
    (irule ptr_mixed_vars_retained_births_tvar >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qexistsl [`b`, `PTc`, `TGc`, `outs`, `B'`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[Abbr `outs`, Abbr `B'`, ptr_observe_def]]
QED

Finalise ptr_focus_ret_restore
