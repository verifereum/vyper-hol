Theory gasFocusLoweringBridge
Ancestors
  gasFocusConcretizeCutFrameAccess gasFocusConcretizeCutFrameSupport
  gasFocusConcretizeCutTaintWithin gasFocusLayoutStaticPrefixEvents
  gasFocusFmpCutFieldMemory gasFocusFmpCutFieldEvents concretizeStageShape
  o1ComposeSupport gasFocusConcretizeCutCoverage o1PassContract o1SafeUpto
  unitTransformDefs lowerDloadDefs unitMemInv venomPassSchedule venomPassDispatcher

(* C2 and C3 share the raw filling. C4 uses the corresponding lowered
   root, while the finite GAS prefix can use a different fuel at each stage. *)
Theorem focus_lowering_cut_bridge:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C2 C3 /\
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C3 C4 /\
  o1_ctx_shape C2 /\ o1_ctx_shape C3 /\ o1_ctx_shape C4 /\
  EVERY (o1_fn_row 3) C3.ctx_functions /\ EVERY (o1_fn_row 4) C4.ctx_functions /\
  EVERY ssa_form C2.ctx_functions /\ EVERY all_reachable C2.ctx_functions /\
  EVERY fn_defs_reach_uses C2.ctx_functions /\ ctx_inst_ids_distinct C2 /\
  callee_first names C2.ctx_functions /\
  o1_initial_state_ok root4 /\ root4.vs_fmp = root4.vs_initial_fmp /\
  code_layout_valid root4 /\ root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  dead_wf D /\ o1_safe_upto D lo n C2 root3 /\ alloca_frontier_upto n C2 root3 /\
  max_live_eom C3 = SOME eom /\ fmp_variant_room (SOME fmp) C4 root4 /\
  C2.ctx_entry = SOME name /\ lookup_function name C2.ctx_functions = SOME fn2 /\
  fn_entry_label fn2 = SOME lbl /\
  s3 = root3 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  s4 = root4 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> /\
  n <= LENGTH (gas_events_blocks fuel2 C2 fn2 s3) ==>
  mem_inv (\ctx fn inst s. gas_cut n root4 s ==> lowered_mem_fact eom ctx fn inst s)
    C4 root4 /\
  ?fuel4 fn4. C4.ctx_entry = SOME name /\
    lookup_function name C4.ctx_functions = SOME fn4 /\ fn_entry_label fn4 = SOME lbl /\
    n <= LENGTH (gas_events_blocks fuel4 C4 fn4 s4) /\
    TAKE n (gas_events_blocks fuel4 C4 fn4 s4) = TAKE n (gas_events_blocks fuel2 C2 fn2 s3)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `o1_initial_state_ok root3 /\ root3.vs_fmp = root3.vs_initial_fmp /\
   code_layout_valid root3` by
    (simp[] >> gvs[o1_initial_state_ok_def, code_layout_valid_def]) >>
  `o1_pre 3 C3 C4` by simp[o1_pre_def] >>
  `o1_ptr_safe_upto D lo n C2 root3` by fs[o1_safe_upto_def] >>
  `EVERY (\fn. fn.fn_eom = NONE) C2.ctx_functions /\ fmp_free_ctx C2` by
    fs[o1_ptr_safe_upto_def] >>
  drule_all_then assume_tac concretize_stage_ssa_form >>
  drule_all_then assume_tac concretize_stage_fmp_free >>
  drule_all_then assume_tac concretize_stage_callee_first >>
  `max_live_eom C4 = SOME eom` by
    (drule ctx_pass_stage_max_live_eom >>
     simp[fn_pass_tag_def,fn_pass_static_layout_effect_def]) >>
  `eom <= w2n root4.vs_initial_fmp /\ w2n root4.vs_initial_fmp <= w2n fmp` by
    fs[fmp_variant_room_def] >>
  `eom <= w2n root3.vs_initial_fmp` by simp[] >>
  `(ctx_has_dalloca C2 ==> eom <= w2n root3.vs_initial_fmp)` by simp[] >>
  drule_all_then (assume_tac o CONJUNCT1) focus_concretize_cut_fields >>
  drule_all_then assume_tac focus_concretize_cut_taint_within >>
  `!fn inst s. raw_reachable root3 C3 fn inst s /\ gas_cut n root3 s ==>
     dalloca_no_wrap inst s` by
    (qpat_assum `mem_inv _ C3 root3` (mp_tac o PURE_REWRITE_RULE [mem_inv_raw_reachable]) >>
     simp[NoAsms, static_mem_ok_def] >> metis_tac[]) >>
  `!stk PG G tn fn inst s.
      frame_reachable root3 C3 stk PG G tn fn inst s /\ gas_cut n root3 s ==>
      access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
      allocas_from eom s /\ (ctx_has_dalloca C3 ==> allocas_below_fmp s) /\
      (?P. fn_static_ptr_ok P fn /\ ptr_use_static_ok P (fn_pv P fn) inst /\
           FDOM G SUBSET fn_pv P fn)` by
    (rpt gen_tac >> strip_tac >>
     drule_all_then strip_assume_tac focus_concretize_cut_frame_access >>
     drule_all_then strip_assume_tac focus_concretize_cut_frame_support >>
     simp[] >> goal_assum drule >> simp[]) >>
  `ctx_has_dalloca C2 ==> ?m. max_live_eom C3 = SOME m /\ m <= w2n root3.vs_initial_fmp` by simp[] >>
  `?fuel3 fn3. C3.ctx_entry = SOME name /\
     lookup_function name C3.ctx_functions = SOME fn3 /\ fn_entry_label fn3 = SOME lbl /\
     n <= LENGTH (gas_events_blocks fuel3 C3 fn3 s3) /\
     TAKE n (gas_events_blocks fuel3 C3 fn3 s3) = TAKE n (gas_events_blocks fuel2 C2 fn2 s3)` by
    (irule focus_layout_stage_prefix_events_static >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  conj_tac >- (drule_all focus_fmp_cut_target_memory_fields >> simp[]) >>
  `!stk PG G tn fn inst s.
      frame_reachable root3 C3 stk PG G tn fn inst s /\ gas_cut n root3 s ==>
      access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
      (?P. fn_static_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
           ptr_use_static_ok P (fn_pv P fn) inst)` by metis_tac[] >>
  drule_all focus_fmp_cut_prefix_events_fields >>
  disch_then (qx_choose_then `fn4` strip_assume_tac) >>
  `C4.ctx_entry = SOME name` by fs[ctx_pass_stage_def] >>
  qexistsl [`fuel4`, `fn4`] >> simp[]
QED
