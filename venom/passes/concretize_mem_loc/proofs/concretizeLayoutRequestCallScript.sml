Theory concretizeLayoutRequestCall
Ancestors concretizeLayoutRequestRelations concretizeLayoutCanonicalCallReturn
  concretizeLayoutCanonicalCallExit concretizeLayoutCanonicalCallEntry
  concretizeLayoutCanonicalDriver concretizeLayoutCanonicalDeferred
  concretizeLayoutCallResult concretizeLayoutPhaseOrigin
  calleeTransport frameSelectedSimulation
  frameFiniteJointDecoration frameFiniteExecution list arithmetic

Theorem layout_request_call_return_certificate_fuel:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  layout_cut_safe D lo ncut vs0 C qend /\
  joint_trace vs0 C q0 es qs qend /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) ==>
  selected_call_return_certificate_fuel C C' q0 path
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> rewrite_tac[selected_call_return_certificate_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  drule layout_request_ES_forget >> strip_tac >>
  `joint_segment C qc wc qe` by metis_tac[cj 3 decorated_execution_segment] >>
  drule_all layout_canonical_call_entry >> strip_tac >> gvs[] >>
  qexistsl [`out`, `ct`] >> conj_tac >- simp[] >>
  rpt strip_tac >> Cases_on `run_blocks k C' out ct` >>
  gvs[layout_request_OutR_def, layout_canonical_OutR_def, layout_canonical_result_def] >>
  rename1 `layout_canonical_ret _ _ _ _ _ _ _ _ _ _ _ _ ret send ret' tend` >>
  `?b. layout_ret_endpoint D lo vs0 C C' q0 (MAP FST path) (MAP SND path)
      qend b send tend ret ret'` by
    (fs[layout_canonical_ret_def] >> metis_tac[]) >>
  drule_all layout_canonical_caller_bind >> strip_tac >>
  pure_rewrite_tac[selected_step_match_fuel_def] >> qexists `OK post'` >>
  conj_tac
  >- simp[Once venomExecSemanticsTheory.step_inst_def] >>
  conj_tac
  >- (irule finite_step_invoke_return >> simp[] >> metis_tac[]) >>
  rewrite_tac[layout_request_OS_def] >> conj_tac
  >- (simp_tac std_ss [LENGTH, ADD_CLAUSES, ADD_COMM] >>
      irule (SIMP_RULE std_ss [LENGTH, ADD_CLAUSES, ADD_COMM]
        (Q.INST [`n` |-> `phase.lop_cursor`]
          layout_canonical_return_deferred)) >>
      goal_assum (drule_at Any) >> simp[] >>
      conj_tac >- metis_tac[] >>
      qexistsl [`dc`, `qc`, `ret`, `ret'`, `send`, `tend`] >> simp[]) >>
  simp[layout_request_state_def] >>
  drule layout_canonical_ret_requests >>
  fs[layout_request_state_def] >> strip_tac >>
  imp_res_tac bind_outputs_oracle >> fs[]
QED

Theorem layout_request_call_exit_certificate_fuel:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  layout_cut_safe D lo ncut vs0 C qend /\
  joint_trace vs0 C q0 es qs qend /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) ==>
  selected_call_exit_certificate_fuel C C' q0 path
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> rewrite_tac[selected_call_exit_certificate_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  drule layout_request_ES_forget >> strip_tac >>
  `joint_segment C qc wc qe` by metis_tac[cj 3 decorated_execution_segment] >>
  drule_all layout_canonical_call_entry >> strip_tac >> gvs[] >>
  qexistsl [`out`, `ct`] >> conj_tac >- simp[] >>
  rpt strip_tac >> Cases_on `run_blocks k C' out ct` >>
  gvs[layout_request_OutR_def, layout_canonical_OutR_def, layout_canonical_result_def] >>
  pure_rewrite_tac[selected_step_match_fuel_def] >>
  (qexists `run_blocks k C' out ct` >>
   conj_tac >- simp[Once venomExecSemanticsTheory.step_inst_def] >>
   conj_tac
   >- (irule finite_step_invoke_exit >> simp[] >> metis_tac[]) >>
   simp[layout_request_OS_def, layout_deferred_OS_def,
        layout_canonical_OS_def, layout_canonical_result_def])
QED

val _ = export_theory();
