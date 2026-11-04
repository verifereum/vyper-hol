Theory ifexpTransportInterface
Ancestors
  exprSim

Theorem expr_val_rel_nonword_transport[local]:
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\
  ~is_word_type src /\ ~is_word_type dst /\
  (!b mem. val_in_memory sv v b mem ==> val_in_memory dv v b mem) /\
  expr_val_rel cx src v op s ==>
  expr_val_rel cx dst v op s
Proof
  simp[expr_val_rel_def] >> metis_tac[]
QED

Theorem expr_val_at_nonword_transport[local]:
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\
  ~is_word_type src /\ ~is_word_type dst /\ val_wf dv v /\
  val_footprint sv v = val_footprint dv v /\
  (dynarray_type src ==> dynarray_type dst) /\
  expr_val_at cenv cx src sa sb es v op s ==>
  expr_val_at cenv cx dst sa sb es v op s
Proof
  strip_tac >> fs[expr_val_at_def] >>
  first_x_assum (qspec_then `sv` mp_tac) >> simp[] >>
  strip_tac >> qexists_tac `w` >> simp[]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >>
  simp[] >> metis_tac[]
QED
