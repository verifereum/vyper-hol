Theory concretizeLayoutScopedRun
Ancestors concretizeLayoutRunEntry concretizeLayoutRunState
  concretizeLayoutScopedPhase concretizeLayoutPhaseOrigin
  frameScopedPhaseCertificates frameIndexedCertificates
  venomExecSemantics venomState contextCodegenRel

Definition layout_scoped_run_def:
  layout_scoped_run D lo vs0 C C' q0 es qs q
    (g:layout_ordinary_phase + layout_terminal_phase) fn fn' s t <=>
  ?a p p'. enters_block fn s p /\ enters_block fn' t p' /\
    ~a.lop_pending /\ layout_ordinary_trace vs0 C q0 es qs q a p /\
    layout_ordinary_state D lo C' q0 es qs a p p'
End

Theorem layout_scoped_run_intro:
  enters_block fn s p /\ enters_block fn' t p' /\ ~a.lop_pending /\
  layout_ordinary_trace vs0 C q0 es qs q a p /\
  layout_ordinary_state D lo C' q0 es qs a p p' ==>
  layout_scoped_run D lo vs0 C C' q0 es qs q g fn fn' s t
Proof
  simp[layout_scoped_run_def] >> metis_tac[]
QED

Theorem layout_scoped_run_phi:
  scoped_phase_phi (layout_scoped_run D lo vs0 C C' q0 es qs q)
    (\g s. T) (layout_scoped_entry D lo vs0 C C' q0 es qs q)
    (\bb bb'. T) layout_scoped_phi_link
Proof
  rw[scoped_phase_phi_def, layout_scoped_run_def] >>
  drule_all (SRULE[layout_scoped_phi_link_def] layout_scoped_enters_entry) >>
  strip_tac >>
  fs[enters_block_def] >> gvs[] >>
  simp[indexed_entry_def, layout_scoped_phi_link_def] >>
  qrefine `INL h` >> simp[layout_scoped_entry_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem layout_scoped_run_initial:
  enters_block fn s p /\ EVERY bb_well_formed fn.fn_blocks /\
  joint_trace vs0 C q0 es qs q /\
  q0 = JointConfig [] [] FEMPTY entry_taint fn inst p [] FEMPTY hs h /\
  p.vs_allocas = FEMPTY ==>
  layout_scoped_run D lo vs0 C C' q0 es qs q g fn
    (concretize_function_with_positions positions fn) s s
Proof
  strip_tac >>
  drule_all (SRULE[layout_scoped_phi_link_def] layout_scoped_initial_enters_entry) >>
  disch_then (qspecl_then [`positions`, `lo`, `D`, `C'`] strip_assume_tac) >>
  drule_all layout_run_initial_state >>
  disch_then (qspecl_then [`ARB`, `lo`, `D`, `C'`] strip_assume_tac) >>
  irule layout_scoped_run_intro >> goal_assum (drule_at Any) >> simp[]
QED

val _ = export_theory();
