Theory concretizeLayoutStageSimulation
Ancestors frameGasEvents gasEvents concretizeLayoutCanonicalContract concretizeLayoutStageEntry
  frameSelectedSimulation frameDecorationComplete frameResolvedCoherent
  frameFiniteJointDecoration frameJointTrace frameSelectedDecoration list
  concretizePtrParamShape unitTransformDefs o1PassContract ptrDiscipline
  venomExecSemantics passSimulationDefs frameFiniteExecution frameFiniteJointTrace
  frameJointTransition venomWf contextCodegenRel o1ContractSimplifyCfg
  concretizeStepStructure concretizeLayoutCanonicalDriver
  concretizeLayoutStagePairing concretizeMemLocDefs

(* The generic selected driver is the only recursive simulation used here. *)
Theorem layout_stage_selected_run:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ taint_within D C vs0 /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  joint_trace vs0 C q0 es qs qend /\
  decorated_run C fn s r q n w qe d /\
  selected_segment C q0 path n q w qe /\
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t ==>
  ?r'. finite_run C' fn' t r' /\
    layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend
      q n qe (n + LENGTH w) fn s fn' t r r' /\
    run_events_agree C C' fn s fn' t r r'
Proof
  strip_tac >>
  `selected_simulation_contract C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (events_OS C C' (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend))
    (events_OB C C' (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend))
    (events_OutR C C' (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend))` by
    (irule layout_canonical_simulation_contract >> metis_tac[]) >>
  drule_all selected_run_simulation >>
  simp[selected_run_match_def, events_OutR_def]
QED

Theorem layout_segment_chain[local]:
  !w q qe. joint_segment C q w qe ==>
    joint_chain C q (MAP FST w) (MAP SND w) qe
Proof
  Induct >> simp[joint_segment_def, joint_chain_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[joint_segment_def, joint_chain_def] >> metis_tac[]
QED

(* One ambient source decoration and one coherent annotation sequence. *)
Theorem layout_stage_source_decoration:
  finite_run C fn s r /\ enters_block fn s p /\
  joint_initial vs0 C q0 /\ decoration_entry fn p q0 /\
  ALL_DISTINCT (fn_labels fn) /\
  EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions /\
  ~ctx_has_dalloca C ==>
  ?path qe d ass.
    decorated_run C fn s r q0 0 path qe d /\
    selected_segment C q0 path 0 q0 path qe /\
    joint_trace vs0 C q0 (MAP FST path) (MAP SND path) qe /\
    EL 0 ass = [([],FEMPTY)] /\
    (!k. k < LENGTH path ==>
      resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
        (EL (SUC k) (q0::MAP SND path))
        (EL k (lifetime_annotations 0 [0] (MAP FST path))) (EL k ass)
        (EL (SUC k) (lifetime_annotations 0 [0] (MAP FST path)))
        (EL (SUC k) ass))
Proof
  strip_tac >> drule (cj 3 finite_decoration_complete) >>
  disch_then (qspecl_then [`q0`, `0`, `p`] mp_tac) >>
  simp[] >> strip_tac >>
  `joint_segment C q0 w qe` by metis_tac[cj 3 decorated_execution_segment] >>
  `joint_trace vs0 C q0 (MAP FST w) (MAP SND w) qe` by
    (simp[joint_trace_def] >> metis_tac[layout_segment_chain]) >>
  drule_all joint_trace_coherent_annotations >> strip_tac >>
  qexistsl [`w`, `qe`, `d`, `ass`] >> simp[] >>
  simp[selected_segment_def, joint_segment_def] >>
  rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >>
  simp[EL_MAP]
QED

(* Root entry: the target run terminates with the source's GAS events. *)
Theorem layout_stage_terminating_events:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  terminates (run_context fuel C vs) ==>
  ?fuel' name fn fn' lbl.
    C.ctx_entry = SOME name /\ C'.ctx_entry = SOME name /\
    lookup_function name C.ctx_functions = SOME fn /\
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn = SOME lbl /\ fn_entry_label fn' = SOME lbl /\
    dead_result_rel D (run_context fuel C vs) (run_context fuel' C' vs) /\
    terminates (run_context fuel' C' vs) /\
    gas_events_blocks fuel' C' fn'
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) =
    gas_events_blocks fuel C fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
Proof
  strip_tac >>
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  drule o1_ctx_shape_instructions_wf >> strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM]) >>
  qpat_assum `ptr_discipline lo C vs` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[EVERY_MEM] >>
  `?name fn lbl. C.ctx_entry = SOME name /\
     lookup_function name C.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl` by
    (qpat_x_assum `terminates _` mp_tac >>
     Cases_on `C.ctx_entry` >>
     simp[run_context_def, passSimulationDefsTheory.terminates_def] >>
     rename1 `lookup_function nm C.ctx_functions` >>
     Cases_on `lookup_function nm C.ctx_functions` >>
     simp[passSimulationDefsTheory.terminates_def] >>
     rename1 `run_function _ _ f0` >>
     Cases_on `fn_entry_label f0` >>
     simp[run_function_def, passSimulationDefsTheory.terminates_def]) >>
  `run_context fuel C vs =
   run_blocks fuel C fn
     (vs with <|vs_current_bb := lbl; vs_inst_idx := 0; vs_prev_bb := NONE|>)` by
    simp[run_context_def, run_function_def] >>
  qabbrev_tac `s =
    vs with <|vs_current_bb := lbl; vs_inst_idx := 0; vs_prev_bb := NONE|>` >>
  `!k G g. G.ctx_entry = SOME name /\ lookup_function name G.ctx_functions = SOME g /\
     fn_entry_label g = SOME lbl ==> run_context k G vs = run_blocks k G g s` by
    (rw[run_context_def, run_function_def, Abbr `s`] >> AP_TERM_TAC >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `!e. run_blocks fuel C fn s <> Error e` by
    (rpt strip_tac >> qpat_x_assum `terminates _` mp_tac >>
     simp[passSimulationDefsTheory.terminates_def]) >>
  `finite_run C fn s (run_blocks fuel C fn s)` by
    metis_tac[cj 3 finite_execution_complete] >>
  drule finite_run_entry_active >> strip_tac >>
  qabbrev_tac `r = run_blocks fuel C fn s` >>
  qabbrev_tac `q0 = JointConfig [] [] FEMPTY entry_taint fn inst' p [] FEMPTY []
    [OriginInitial s; OriginObserve (OriginSnapshot fn [] FEMPTY FEMPTY inst' p)]` >>
  `joint_initial vs C q0` by
    (fs[Abbr `q0`, Abbr `s`] >> metis_tac[joint_initial_entry]) >>
  `decoration_entry fn p q0` by
    (simp[decoration_entry_def, decoration_at_def, Abbr `q0`] >> metis_tac[]) >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `wf_function fn /\ fn.fn_eom = NONE` by fs[EVERY_MEM] >>
  `ALL_DISTINCT (fn_labels fn) /\
    EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions` by
    fs[wf_function_def, EVERY_MEM] >>
  drule_all layout_stage_source_decoration >> strip_tac >>
  `EVERY bb_well_formed fn.fn_blocks` by fs[wf_function_def, EVERY_MEM] >>
  `s.vs_allocas = FEMPTY` by simp[Abbr `s`] >>
  `?fn' positions.
     lookup_function name C'.ctx_functions = SOME fn' /\
     layout_driver_row C' fn fn' positions /\
     layout_canonical_run D lo vs C C' q0 (MAP FST path) (MAP SND path)
       ass qe q0 0 fn s fn' s` by
    (irule layout_stage_entry_initial >>
     goal_assum (drule_at Any) >> simp[Abbr `q0`] >> metis_tac[]) >>
  `activation_depth q0 = 0` by simp[Abbr `q0`, frameActivationCacheTheory.activation_depth_def] >>
  `?r'. finite_run C' fn' s r' /\
    layout_canonical_OutR D lo vs C C' q0 (MAP FST path) (MAP SND path)
      ass qe q0 0 qe (0 + LENGTH path) fn s fn' s r r' /\
    run_events_agree C C' fn s fn' s r r'` by
    (irule layout_stage_selected_run >> metis_tac[]) >>
  `!ret t. r <> IntRet ret t` by
    (drule o1_ctx_shape_no_intret >>
     disch_then (qspecl_then [`fuel`, `vs`] mp_tac) >>
     simp[run_context_def, run_function_def, Abbr `r`, Abbr `s`]) >>
  `dead_result_rel D r r'` by
    (fs[layout_canonical_OutR_def] >>
     Cases_on `r` >> Cases_on `r'` >> gvs[layout_canonical_result_def]) >>
  `C'.ctx_entry = SOME name` by fs[ctx_pass_stage_def] >>
  `fn_entry_label fn' = SOME lbl` by
    (fs[layout_driver_row_def, layout_stage_row_def,
        apply_context_concretize_layout_def, apply_concretize_layout_def,
        venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
     qspecl_then [`layout.cl_positions`, `fn`] mp_tac
       (GEN_ALL concretize_positions_entry_label) >>
     simp[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def]) >>
  qpat_assum `finite_run C' fn' s r'`
    (strip_assume_tac o MATCH_MP (cj 3 finite_execution_realizable)) >>
  `run_blocks n C' fn' s = r'` by simp[] >>
  `!e. r' <> Error e` by metis_tac[cj 3 finite_execution_nonerror] >>
  `terminates r'` by
    (qpat_x_assum `!e. r' <> Error e` mp_tac >>
     Cases_on `r'` >> simp[passSimulationDefsTheory.terminates_def]) >>
  `run_context n C' vs = r'` by metis_tac[] >>
  `gas_events_blocks n C' fn' s = gas_events_blocks fuel C fn s` by
    (qunabbrev_tac `r` >>
     qpat_x_assum `run_events_agree _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [run_events_agree_def]) >>
     disch_then (qspecl_then [`fuel`, `n`] mp_tac) >> simp[]) >>
  `vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> = s` by
    simp[Abbr `s`, venomStateTheory.venom_state_component_equality] >>
  qexistsl [`n`, `name`, `fn`, `fn'`, `lbl`] >>
  pop_assum (fn th => rewrite_tac[th]) >> simp[]
QED

Theorem layout_stage_terminating_context:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  terminates (run_context fuel C vs) ==>
  ?fuel'. dead_result_rel D (run_context fuel C vs) (run_context fuel' C' vs)
Proof
  strip_tac >> mp_tac layout_stage_terminating_events >>
  impl_tac >- metis_tac[] >> metis_tac[]
QED

val _ = export_theory();
