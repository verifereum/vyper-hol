(*
 * ConcretizeMemLoc's request companion: an aborting run of the input
 * context is matched by an aborting run of the output whose requests are a
 * prefix of the input's up to the dead bytes (ctx_abort_rq), under
 * concretize_stage_sim's premises.
 *)
Theory concretizeStageRequests
Ancestors
  concretizeStageSim o1RequestContract o1PassContract ptrDiscipline
  unitMemInv concretizeMemLocDefs venomPassDispatcher cfgWf
  concretizeLayoutStageSimulation concretizeLayoutCorridorRequests
  concretizeLayoutRequestRelations concretizeLayoutRequestRun
  concretizeLayoutRequestBase concretizeLayoutRequestBlock
  concretizeLayoutRequestControl concretizeLayoutRequestSimulation
  frameFiniteExecution frameFiniteJointTrace frameJointTransition
  frameSelectedDecoration frameActivationCache concretizeLayoutStageEntry
  concretizeLayoutStagePairing concretizeLayoutCanonicalDriver
  concretizePtrParamShape unitTransformDefs venomExecSemantics
  concretizeStepStructure list frameDecorationComplete venomWf
  frameFiniteJointDecoration

(* The scheduled row retains the source entry label. *)
Theorem layout_driver_row_entry_label:
  layout_driver_row C' fn fn' positions ==>
  fn_entry_label fn' = fn_entry_label fn
Proof
  simp[layout_driver_row_def, layout_stage_row_def] >> strip_tac >>
  gvs[apply_context_concretize_layout_def, apply_concretize_layout_def,
      venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
  qspecl_then [`layout.cl_positions`, `fn`] mp_tac
    (GEN_ALL concretize_positions_entry_label) >>
  simp[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def]
QED

(* Decorate a finite source abort once, initialize the selected driver at
   the actual scheduled function, and retain its request observation. *)
Theorem layout_stage_request_finite_abort:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  s = vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |> /\
  finite_run C fn s (Abort a post) ==>
  ?fn' b post'. lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\ finite_run C' fn' s (Abort b post') /\
    LIST_REL (request_agree_except D) post.vs_requests post'.vs_requests
Proof
  strip_tac >>
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  drule o1_ctx_shape_instructions_wf >> strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  qpat_assum `ptr_discipline lo C vs` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[EVERY_MEM] >>
  drule finite_run_entry_active >> strip_tac >> rename1 `active_inst fn inst p` >>
  qabbrev_tac `q0 = JointConfig [] [] FEMPTY entry_taint fn inst p [] FEMPTY []
    [OriginInitial s; OriginObserve (OriginSnapshot fn [] FEMPTY FEMPTY inst p)]` >>
  `joint_initial vs C q0` by
    (simp[Abbr `q0`] >> metis_tac[joint_initial_entry]) >>
  `decoration_entry fn p q0` by
    (simp[decoration_entry_def, decoration_at_def, Abbr `q0`] >> metis_tac[]) >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `wf_function fn /\ fn.fn_eom = NONE` by fs[EVERY_MEM] >>
  `ALL_DISTINCT (fn_labels fn) /\
    EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions` by
    fs[wf_function_def, EVERY_MEM] >>
  drule_all layout_stage_source_decoration >> strip_tac >>
  `EVERY bb_well_formed fn.fn_blocks` by fs[wf_function_def, EVERY_MEM] >>
  `s.vs_allocas = FEMPTY` by simp[] >>
  `?fn' positions.
     lookup_function name C'.ctx_functions = SOME fn' /\
     layout_driver_row C' fn fn' positions /\
     layout_canonical_run D lo vs C C' q0 (MAP FST path) (MAP SND path)
       ass qe q0 0 fn s fn' s` by
    (irule layout_stage_entry_initial >>
     goal_assum (drule_at Any) >> simp[Abbr `q0`] >> metis_tac[]) >>
  `activation_depth q0 = 0` by simp[Abbr `q0`, activation_depth_def] >>
  `?r'. finite_run C' fn' s r' /\
    layout_request_OutR D lo vs C C' q0 (MAP FST path) (MAP SND path)
      ass qe q0 0 qe (0 + LENGTH path) fn s fn' s (Abort a post) r'` by
    (irule layout_stage_request_selected_run >> metis_tac[]) >>
  drule layout_request_OutR_abort >> strip_tac >>
  qexistsl [`fn'`, `b`, `post'`] >>
  metis_tac[layout_driver_row_entry_label]
QED

Theorem concretize_stage_abort_rq:
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
  EVERY fn_defs_reach_uses C.ctx_functions ==>
  ctx_abort_rq D C C' vs vs
Proof
  strip_tac >> simp[ctx_abort_rq_def] >> rpt strip_tac >>
  Cases_on `C.ctx_entry` >> gvs[run_context_def] >>
  rename1 `C.ctx_entry = SOME name` >>
  Cases_on `lookup_function name C.ctx_functions` >> gvs[] >>
  rename1 `lookup_function name C.ctx_functions = SOME fn` >>
  Cases_on `fn_entry_label fn` >> gvs[run_function_def] >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  qmatch_asmsub_abbrev_tac `run_blocks fuel C fn s` >>
  `finite_run C fn s (Abort a t)` by
    (qpat_assum `run_blocks fuel C fn s = Abort a t` (SUBST1_TAC o SYM) >>
     irule (cj 3 finite_execution_complete) >> simp[]) >>
  `?fn' b post'. lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\ finite_run C' fn' s (Abort b post') /\
    LIST_REL (request_agree_except D) t.vs_requests post'.vs_requests` by
    (irule layout_stage_request_finite_abort >>
     simp[Abbr `s`] >> metis_tac[]) >>
  `C'.ctx_entry = SOME name` by fs[ctx_pass_stage_def] >>
  drule (cj 3 finite_execution_realizable) >> strip_tac >>
  qexistsl [`n`, `b`, `post'`] >>
  conj_tac
  >- (first_x_assum (qspec_then `n` mp_tac) >> simp[Abbr `s`]) >>
  irule LIST_REL_imp_request_prefix_rel >> simp[]
QED
