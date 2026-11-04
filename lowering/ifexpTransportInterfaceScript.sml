Theory ifexpTransportInterface
Ancestors
  exprSim vyperTypeSystem vyperValue valueEncoding

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

Theorem evaluated_layout_size:
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) /\
  evaluate_type tenv src = SOME sv /\
  evaluate_type tenv dst = SOME dv /\
  type_memory_bytes cenv src = type_memory_bytes cenv dst ==>
  type_memory_size sv = type_memory_size dv
Proof
  metis_tac[]
QED

Theorem compatible_base_memory:
  arg_type_fits (BaseT src) (BaseT dst) /\
  evaluate_type tenv (BaseT src) = SOME sv /\
  evaluate_type tenv (BaseT dst) = SOME dv ==>
  (val_in_memory sv v b mem <=> val_in_memory dv v b mem)
Proof
  Cases_on `src` >> Cases_on `dst` >>
  simp[arg_type_fits_def] >> rpt strip_tac >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs(), arg_type_fits_def] >>
  Cases_on `v` >> simp[val_in_memory_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> simp[val_in_memory_def]
QED
