Theory concretizeLayoutCanonicalCallExit
Ancestors frameGasEvents concretizeLayoutCanonicalCallEntry concretizeLayoutCanonicalDriver frameSelectedSimulation
  frameFiniteJointDecoration frameFiniteExecution list arithmetic

Theorem layout_canonical_call_exit_certificate:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ptr_discipline lo C vs0 /\ vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs qend /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) ==>
  selected_call_exit_certificate C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (events_OS C C' (layout_canonical_OS D lo vs0 C C' q0 es qs ass qend))
    (events_OutR C C' (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend))
Proof
  strip_tac >> rewrite_tac[selected_call_exit_certificate_def] >>
  rpt gen_tac >> strip_tac >>
  `joint_segment C qc wc qe` by metis_tac[cj 3 decorated_execution_segment] >>
  drule_all layout_canonical_call_entry >> strip_tac >> gvs[] >>
  (qexistsl [`out`, `ct`] >>
   conj_tac >- simp[] >>
   rpt strip_tac >>
   qpat_x_assum `events_OutR _ _ _ _ _ _ _ _ _ _ _ _ _`
     (strip_assume_tac o REWRITE_RULE [events_OutR_def]) >>
   rename1 `finite_run _ _ _ result` >>
   simp[selected_step_match_def] >>
   qexists `result` >>
   Cases_on `result` >>
   gvs[layout_canonical_OutR_def, layout_canonical_result_def] >>
   (conj_tac
    >- (irule finite_step_invoke_exit >> simp[] >> metis_tac[]) >>
    simp[events_OS_def, layout_canonical_OS_def, layout_canonical_result_def] >>
    irule step_events_agree_invoke >> simp[] >>
    metis_tac[cj 3 decorated_execution_erases]))
QED

val _ = export_theory();
