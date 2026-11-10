Theory fnPlanLineageNativeTrace
Ancestors
  fnPlanLineageCallTrace fnPlanLineageChronologicalPrefix
  fnPlanLineageNativeTerminal fnPlanLineageNativeOrigins
  fnPlanLineageEntryProduction fnPlanLineageLiveness stackPlanGen venomWf venomInst
  codegenReadyCompute list rich_list pred_set

Theorem initialized_entry_exit_support:
  !fn entry bb dfg ch growth spill_base lbl_ctr ops qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block entry fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) = SOME (ops,qs) ==>
    chronological_support fn [entry] qs /\
    native_live_boundary fn bb (LENGTH bb.bb_instructions) qs
Proof
  rpt gen_tac >> strip_tac >>
  `fn.fn_blocks <> [] /\ bb = HD fn.fn_blocks /\ bb.bb_label = entry` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
  gvs[] >> drule_all initialized_entry_exit_origins >> strip_tac >>
  drule_all initialized_entry_exit_live_boundary >> strip_tac >>
  simp[] >> gvs[chronological_support_def, prefix_inventory_origins_def] >>
  rpt strip_tac >> qexists_tac `HD fn.fn_blocks` >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  metis_tac[EL_MEM]
QED

Theorem singleton_trace_first[local]:
  plan_aux_trace lv dfg cfg fn [root] [] ps result events ==>
  ?tail. events = (root,ps)::tail
Proof
  simp[Once plan_aux_trace_cases] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem initialized_trace_event_certificate_by_length[local]:
  !n fn entry dfg ch growth spill_base lbl_ctr result events pre lbl ps post.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    plan_aux_trace (liveness_analyze fn) dfg (cfg_analyze fn) fn [entry] []
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) result events /\
    events = pre ++ (lbl,ps)::post /\ LENGTH pre = n ==>
    cfg_reachable_of (cfg_analyze fn) lbl /\
    (!bb ops qs. lookup_block lbl fn.fn_blocks = SOME bb /\
      generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb ps = SOME (ops,qs) ==>
      chronological_support fn (lbl::MAP FST pre) qs /\
      native_live_boundary fn bb (LENGTH bb.bb_instructions) qs)
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  drule_all plan_aux_trace_singleton_physical_ancestry >> strip_tac
  >- (gvs[] >> conj_tac
      >- metis_tac[analyzed_entry_reachable] >>
      metis_tac[initialized_entry_exit_support]) >>
  `?earlier rest. pre = earlier ++ (pred,before)::rest` by metis_tac[MEM_SPLIT] >>
  `LENGTH earlier < n` by (gvs[] >> simp[] >> decide_tac) >>
  `cfg_reachable_of (cfg_analyze fn) pred /\
   chronological_support fn (pred::MAP FST earlier) after /\
   native_live_boundary fn bb (LENGTH bb.bb_instructions) after` by
    (first_x_assum (qspec_then `LENGTH earlier` mp_tac) >>
     (impl_tac >- decide_tac) >>
     disch_then (drule_at (Pat `plan_aux_trace _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> disch_then (qspec_then `earlier` mp_tac) >>
     simp[]) >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by metis_tac[analyzed_successor_reachable] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `~MEM lbl (MAP FST pre)` by
    (drule plan_aux_trace_distinct_keys >> simp[MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `lbl <> entry` by
    (drule singleton_trace_first >> strip_tac >>
     Cases_on `pre` >> gvs[]) >>
  `chronological_support fn (MAP FST pre) after` by
    (irule chronological_support_mono >> goal_assum (drule_at Any) >>
     gvs[MAP_APPEND, SUBSET_DEF] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `fn_reachable fn lbl` by metis_tac[fn_reachable_cfg_analyze] >>
  `bb'.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  qpat_x_assum `!m. _` kall_tac >>
  metis_tac[incoming_nonentry_block_exit]
QED

Theorem initialized_trace_event_reachable:
  !fn entry dfg ch growth spill_base lbl_ctr result events pre lbl ps post.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    plan_aux_trace (liveness_analyze fn) dfg (cfg_analyze fn) fn [entry] []
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) result events /\
    events = pre ++ (lbl,ps)::post ==>
    cfg_reachable_of (cfg_analyze fn) lbl /\ fn_reachable fn lbl
Proof
  rpt gen_tac >> strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by
    metis_tac[initialized_trace_event_certificate_by_length] >>
  gvs[codegen_ready_fn_def] >> metis_tac[fn_reachable_cfg_analyze]
QED

Theorem initialized_trace_event_exit:
  !fn entry dfg ch growth spill_base lbl_ctr result events pre lbl ps post bb ops qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    plan_aux_trace (liveness_analyze fn) dfg (cfg_analyze fn) fn [entry] []
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) result events /\
    events = pre ++ (lbl,ps)::post /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb ps = SOME (ops,qs) ==>
    chronological_support fn (lbl::MAP FST pre) qs /\
    native_live_boundary fn bb (LENGTH bb.bb_instructions) qs
Proof
  metis_tac[initialized_trace_event_certificate_by_length]
QED
