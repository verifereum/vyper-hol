Theory concretizeLayoutRequestRun
Ancestors concretizeLayoutRequestRelations concretizeLayoutCanonicalRunNext
  concretizeLayoutCanonicalRunExit concretizeLayoutCanonicalDriver
  concretizeLayoutCanonicalBlock concretizeLayoutCompletedJump
  concretizeLayoutCanonicalDeferred concretizeLayoutPairedEntry
  frameSelectedSimulation frameFiniteExecution frameFiniteControl
  frameFiniteJointDecoration venomExecSemantics venomState list arithmetic

(* The shared phi witness exposes the precise endpoint at which requests
   are observed.  No block certificate implementation is needed here. *)
Theorem layout_request_run_block_entry:
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t /\
  EVERY wf_function C.ctx_functions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK phi /\
  decoration_entry fn (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q ==>
  ?bb' phi'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    eval_phis t bb'.bb_instructions = OK phi' /\
    layout_request_EB D lo vs0 C C' q0 es qs ass qend q n bb
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb'
      (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
Proof
  strip_tac >> drule_all layout_canonical_run_block_entry >> strip_tac >>
  qexistsl [`bb'`, `phi'`] >> simp[layout_request_EB_def] >>
  drule layout_canonical_run_requests >> strip_tac >>
  drule_all layout_request_state_phis >>
  simp[layout_request_state_def]
QED

Theorem layout_request_run_next_certificate:
  vs0.vs_allocas = FEMPTY /\ EVERY wf_function C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) ==>
  selected_run_next_certificate C C' q0 path
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> simp[selected_run_next_certificate_def] >> rpt gen_tac >> strip_tac >>
  drule_all layout_request_run_block_entry >> strip_tac >>
  qexistsl [`bb'`, `phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions`] >>
  simp[] >> gen_tac >> strip_tac >>
  `?v. rb' = OK v` by
    (Cases_on `rb'` >> fs[layout_request_OB_def, layout_canonical_OB_def,
       layout_canonical_result_def]) >> gvs[] >>
  qexists `v` >> conj_tac
  >- (fs[layout_request_EB_def, layout_request_OB_def] >>
      drule_at (Pat `layout_canonical_OB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
        layout_canonical_run_continue >> simp[] >> metis_tac[]) >>
  gen_tac >> strip_tac >> simp[selected_run_match_def] >> qexists `rr'` >> conj_tac
  >- (irule finite_step_run_next >> goal_assum (drule_at Any) >>
      metis_tac[finite_execution_block_endpoint]) >>
  qpat_x_assum `layout_request_OutR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[layout_request_OutR_def, layout_canonical_OutR_def] >> simp[]
QED

Theorem layout_request_run_halt_certificate:
  EVERY wf_function C.ctx_functions ==>
  selected_run_halt_certificate C C' q0 path
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> simp[selected_run_halt_certificate_def] >> rpt gen_tac >> strip_tac >>
  drule_all layout_request_run_block_entry >> strip_tac >>
  qexistsl [`bb'`, `phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions`] >>
  simp[] >> rpt strip_tac >> Cases_on `rb'` >>
  gvs[layout_request_OB_def, layout_canonical_OB_def, layout_canonical_result_def,
    layout_request_EB_def, layout_canonical_EB_def] >>
  first_x_assum drule >> strip_tac >> fs[layout_completed_jump_def]
QED

Theorem layout_request_run_exit_certificate:
  EVERY wf_function C.ctx_functions ==>
  selected_run_exit_certificate C C' q0 path
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> rewrite_tac[selected_run_exit_certificate_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all layout_request_run_block_entry >> strip_tac >>
  qexistsl [`bb'`, `phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions`] >>
  simp[] >> rpt strip_tac >>
  `layout_canonical_result D lo vs0 C C' q0 es qs ass qend qe
    (n + LENGTH w) r rb'` by
    (Cases_on `r` >> Cases_on `rb'` >>
     gvs[layout_request_OB_def, layout_canonical_OB_def]) >>
  `!p. rb' <> OK p` by
    (Cases_on `r` >> Cases_on `rb'` >> gvs[layout_canonical_result_def]) >>
  simp[selected_run_match_def] >> qexists `rb'` >> conj_tac
  >- gvs[finite_step_run_exit] >>
  gvs[layout_request_OutR_def, layout_canonical_OutR_def, layout_request_OB_def]
QED
