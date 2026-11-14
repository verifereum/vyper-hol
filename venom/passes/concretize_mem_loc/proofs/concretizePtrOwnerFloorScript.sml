Theory concretizePtrOwnerFloor
Ancestors concretizePtrOwnerPath concretizePtrHistoryObservation
  concretizePtrChronologicalHistory frameExecutionHistory ptrDiscipline
  concretizeLayoutAccessGeometry concretizeLayoutCutSafe o1SafeUpto
  list rich_list arithmetic

Theorem ptr_reachable_owner_allocas_from_upto:
  ptr_observation_reachable vs C obs /\
  ptr_discipline_upto lo ncut C vs /\ gas_cut ncut vs obs.po_state /\
  d <= LENGTH obs.po_stack ==>
  allocas_from lo (ptr_owner_view d obs).cf_state
Proof
  strip_tac >> fs[ptr_observation_reachable_def] >>
  Cases_on `d = LENGTH obs.po_stack`
  >- (simp[ptr_owner_view_def] >> metis_tac[ptr_discipline_upto_at]) >>
  `LENGTH obs.po_stack - d - 1 < LENGTH obs.po_stack` by decide_tac >>
  drule_all frame_reachable_saved_allocas_from >>
  rewrite_tac[EVERY_EL] >>
  disch_then (qspec_then `LENGTH obs.po_stack - d - 1` mp_tac) >>
  simp[ptr_owner_view_def]
QED

Theorem ptr_reachable_owner_allocas_from:
  ptr_observation_reachable vs C obs /\ ptr_discipline lo C vs /\
  d <= LENGTH obs.po_stack ==>
  allocas_from lo (ptr_owner_view d obs).cf_state
Proof
  strip_tac >> irule ptr_reachable_owner_allocas_from_upto >>
  conj_tac >- simp[] >>
  qexistsl_tac [`C`, `SUC (LENGTH vs.vs_gas_readings)`, `vs`] >>
  simp[] >> metis_tac[ptr_discipline_upto_whole]
QED
