Theory concretizeLayoutCanonicalRunExit
Ancestors concretizeLayoutCanonicalRunNext
  concretizeLayoutCanonicalBlock concretizeLayoutCanonicalDriver
  concretizeLayoutCanonicalDeferred frameSelectedSimulation
  concretizeLayoutStagePairing concretizeLayoutScopedPhase
  concretizeLayoutPhaseOrigin concretizeLayoutPairedEntry


(* Leaf of the canonical simulation contract, run-exit: a block whose
   result is not OK. *)
Theorem layout_canonical_run_exit_certificate:
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
  joint_trace vs0 C q0 es qs qend ==>
  selected_run_exit_certificate C C' q0 path
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> rewrite_tac[selected_run_exit_certificate_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all layout_canonical_run_block_entry >> strip_tac >>
  qexistsl [`bb'`, `phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions`] >>
  simp[] >> rpt strip_tac >>
  `layout_canonical_result D lo vs0 C C' q0 es qs ass qend qe
    (n + LENGTH w) r rb'` by
    (Cases_on `r` >> Cases_on `rb'` >> gvs[layout_canonical_OB_def]) >>
  `!p. rb' <> OK p` by
    (Cases_on `r` >> Cases_on `rb'` >> gvs[layout_canonical_result_def]) >>
  simp[selected_run_match_def, layout_canonical_OutR_def] >>
  qexists `rb'` >> simp[] >>
  gvs[frameFiniteExecutionTheory.finite_step_run_exit]
QED

Theorem layout_canonical_run_exit_certificate_fuel:
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
  joint_trace vs0 C q0 es qs qend ==>
  selected_run_exit_certificate_fuel C C' q0 path
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> rewrite_tac[selected_run_exit_certificate_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all layout_canonical_run_block_entry >> strip_tac >>
  qexistsl [`bb'`, `phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions`] >>
  (conj_tac >- first_assum ACCEPT_TAC) >> rpt gen_tac >> strip_tac >>
  `layout_canonical_result D lo vs0 C C' q0 es qs ass qend qe
    (n + LENGTH w) r rb'` by
    (Cases_on `r` >> Cases_on `rb'` >> gvs[layout_canonical_OB_def]) >>
  `!p. rb' <> OK p` by
    (Cases_on `r` >> Cases_on `rb'` >> gvs[layout_canonical_result_def]) >>
  pure_rewrite_tac[selected_run_match_fuel_def, layout_canonical_OutR_def] >>
  qexists `rb'` >> conj_tac
  >- (simp[Once venomExecSemanticsTheory.run_blocks_def,
           venomExecSemanticsTheory.run_block_def] >> Cases_on `rb'` >> gvs[]) >>
  conj_tac >- metis_tac[frameFiniteExecutionTheory.finite_step_run_exit] >>
  gvs[]
QED

val _ = export_theory();
