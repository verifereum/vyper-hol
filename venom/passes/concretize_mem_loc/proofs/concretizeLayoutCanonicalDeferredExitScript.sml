Theory concretizeLayoutCanonicalDeferredExit
Ancestors concretizeLayoutCutSafe frameGasEvents concretizeLayoutCanonicalCallExit concretizeLayoutCanonicalDeferred
  frameSelectedSimulation



(* Leaf of the canonical simulation contract: the call-exit certificate
   for the deferred OS, from layout_canonical_call_exit_certificate. *)


Theorem layout_deferred_call_exit_certificate_fuel:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  layout_cut_safe D lo ncut vs0 C qend /\ vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs qend /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) ==>
  selected_call_exit_certificate_fuel C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (events_OS C C' (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend))
    (events_OutR C C' (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend))
Proof
  strip_tac >>
  drule_all layout_canonical_call_exit_certificate_fuel >>
  pure_rewrite_tac[selected_call_exit_certificate_fuel_def] >>
  disch_tac >> rpt gen_tac >> strip_tac >>
  (first_x_assum (qspecl_then
    [`k`, `i`, `s`, `name`, `ops`, `fn`, `args`, `cs`, `r`, `caller`,
     `q`, `n`, `qc`, `wc`, `qe`, `dc`, `j`, `t`] mp_tac) >>
   impl_tac >- (fs[] >> metis_tac[]) >> strip_tac >>
  rename1 `layout_canonical_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ target entry` >>
  (qexistsl [`target`, `entry`] >> conj_tac >- first_assum ACCEPT_TAC >>
   rpt gen_tac >> strip_tac >> first_x_assum drule_all >>
   gvs[selected_step_match_fuel_def, events_OS_def, layout_deferred_nonOK]))
QED

val _ = export_theory();
