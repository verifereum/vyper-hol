Theory concretizeLayoutStageSimulation
Ancestors concretizeLayoutCanonicalContract concretizeLayoutStageEntry
  frameSelectedSimulation frameDecorationComplete frameResolvedCoherent
  frameFiniteJointDecoration frameJointTrace frameSelectedDecoration list
  concretizePtrParamShape unitTransformDefs o1PassContract ptrDiscipline
  venomExecSemantics passSimulationDefs frameFiniteExecution frameFiniteJointTrace
  frameJointTransition venomWf contextCodegenRel o1ContractSimplifyCfg
  concretizeStepStructure

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
      q n qe (n + LENGTH w) fn s fn' t r r'
Proof
  strip_tac >>
  `selected_simulation_contract C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend)` by
    (irule layout_canonical_simulation_contract >> metis_tac[]) >>
  drule_all selected_run_simulation >> simp[selected_run_match_def]
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
  strip_tac >>
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  drule o1_ctx_shape_instructions_wf >> strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM]) >>
  qpat_assum `ptr_discipline lo C vs` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[EVERY_MEM] >>
  Cases_on `C.ctx_entry` >>
  gvs[run_context_def, passSimulationDefsTheory.terminates_def] >>
  rename1 `C.ctx_entry = SOME name` >>
  Cases_on `lookup_function name C.ctx_functions` >>
  gvs[passSimulationDefsTheory.terminates_def] >>
  rename1 `lookup_function name C.ctx_functions = SOME fn` >>
  Cases_on `fn_entry_label fn` >>
  gvs[run_function_def, passSimulationDefsTheory.terminates_def] >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  qmatch_goalsub_abbrev_tac `run_blocks fuel C fn s` >>
  `finite_run C fn s (run_blocks fuel C fn s)` by
    (irule (cj 3 finite_execution_complete) >>
     Cases_on `run_blocks fuel C fn s` >> gvs[]) >>
  drule finite_run_entry_active >> strip_tac >>
  qmatch_goalsub_abbrev_tac `dead_result_rel D r _` >>
  qabbrev_tac `q0 = JointConfig [] [] FEMPTY entry_taint fn inst' p [] FEMPTY []
    [OriginInitial s; OriginObserve (OriginSnapshot fn [] FEMPTY FEMPTY inst' p)]` >>
  `joint_initial vs C q0` by
    (simp[Abbr `q0`, Abbr `s`] >> metis_tac[joint_initial_entry]) >>
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
      ass qe q0 0 qe (0 + LENGTH path) fn s fn' s r r'` by
    (irule layout_stage_selected_run >> metis_tac[]) >>
  `!ret t. r <> IntRet ret t` by
    (simp[Abbr `r`, Abbr `s`] >>
     metis_tac[o1_ctx_shape_no_intret, run_context_def, run_function_def]) >>
  `dead_result_rel D r r'` by
    (fs[layout_canonical_OutR_def] >>
     Cases_on `r` >> Cases_on `r'` >> gvs[layout_canonical_result_def]) >>
  `C'.ctx_entry = SOME name` by fs[ctx_pass_stage_def] >>
  `fn_entry_label fn' = SOME lbl` by
    (fs[layout_driver_row_def, layout_stage_row_def,
        apply_context_concretize_layout_def, apply_concretize_layout_def,
        concretize_positions_entry_label]) >>
  simp[] >>
  drule (cj 3 finite_execution_realizable) >> strip_tac >>
  qexists_tac `n` >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[Abbr `s`]

QED

val _ = export_theory();
