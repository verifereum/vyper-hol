Theory concretizePtrOwnerFloor
Ancestors concretizePtrOwnerPath concretizePtrHistoryObservation
  concretizePtrChronologicalHistory frameExecutionHistory ptrDiscipline
  list rich_list arithmetic

Theorem ptr_reachable_owner_allocas_from:
  ptr_observation_reachable vs C obs /\ ptr_discipline lo C vs /\
  d <= LENGTH obs.po_stack ==>
  allocas_from lo (ptr_owner_view d obs).cf_state
Proof
  strip_tac >> fs[ptr_observation_reachable_def] >>
  Cases_on `d = LENGTH obs.po_stack`
  >- (simp[ptr_owner_view_def] >> fs[ptr_discipline_def] >> metis_tac[]) >>
  qabbrev_tac `n = LENGTH obs.po_stack - SUC d` >>
  `n < LENGTH obs.po_stack` by (simp[Abbr `n`] >> decide_tac) >>
  drule frame_reachable_has_history >> strip_tac >>
  drule_all frame_history_saved_endpoint >> strip_tac >>
  `MEM ((EL n obs.po_stack).cf_inst,(EL n obs.po_stack).cf_state) (EL n hs)` by
    metis_tac[MEM_LAST_NOT_NIL] >>
  drule_all ptr_history_saved_observation >> strip_tac >>
  `allocas_from lo (EL n obs.po_stack).cf_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  simp[ptr_owner_view_def, GSYM ADD1, Abbr `n`]
QED
