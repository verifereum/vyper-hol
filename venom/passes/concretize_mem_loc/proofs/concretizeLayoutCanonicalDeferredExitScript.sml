Theory concretizeLayoutCanonicalDeferredExit
Ancestors frameGasEvents concretizeLayoutCanonicalCallExit concretizeLayoutCanonicalDeferred
  frameSelectedSimulation

Theorem deferred_exit_step_match[local]:
  ((?post. r = Halt post) \/ (?a post. r = Abort a post)) ==>
  (selected_step_match C'
     (events_OS C C' (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend))
     q n w qe i s j t r <=>
   selected_step_match C'
     (events_OS C C' (layout_canonical_OS D lo vs0 C C' q0 es qs ass qend))
     q n w qe i s j t r)
Proof
  strip_tac >> gvs[selected_step_match_def, events_OS_def] >>
  simp[layout_deferred_nonOK]
QED

(* Leaf of the canonical simulation contract: the call-exit certificate
   for the deferred OS, from layout_canonical_call_exit_certificate. *)
Theorem layout_deferred_call_exit_certificate:
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
    (events_OS C C' (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend))
    (events_OutR C C' (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend))
Proof
  strip_tac >>
  drule_all layout_canonical_call_exit_certificate >>
  disch_then (qspec_then `D` mp_tac) >>
  rewrite_tac[selected_call_exit_certificate_def] >>
  disch_tac >> rpt gen_tac >> strip_tac >>
  gvs[deferred_exit_step_match] >>
  metis_tac[]
QED

val _ = export_theory();
