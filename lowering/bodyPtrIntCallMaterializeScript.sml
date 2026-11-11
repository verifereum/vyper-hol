Theory bodyPtrIntCallMaterialize
Ancestors
  bodyPtrIntCallEntryContracts ghostObservationPtr
  bodyPtrDefs ptrDiscipline venomState finite_map words list pred_set

Theorem intcall_local_value_transport:
  intcall_local_value entry p sz G tn s /\
  lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
  op_taint un (Var p) = {} /\ s.vs_alloca_next <= t.vs_alloca_next /\
  (!a. a < s.vs_alloca_next ==>
    mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory) /\
  (!a. a < s.vs_alloca_next /\ a IN un.t_mem ==> a IN tn.t_mem) ==>
  intcall_local_value entry p sz H un t
Proof
  strip_tac >> fs[intcall_local_value_def] >>
  conj_tac >- metis_tac[ptr_covers_def] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_no_new_taint >>
  simp[] >> qexists_tac `{a | s.vs_alloca_next <= a}` >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[]
QED

Theorem intcall_completed_transport:
  intcall_completed env ce G tn s /\
  (!p sz name. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
    op_taint un (Var p) = {}) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!a. a < s.vs_alloca_next ==>
    mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory) /\
  (!a. a < s.vs_alloca_next /\ a IN un.t_mem ==> a IN tn.t_mem) ==>
  intcall_completed env ce H un t
Proof
  strip_tac >> simp[intcall_completed_def] >> rpt strip_tac >>
  qpat_x_assum `intcall_completed _ _ _ _ _` mp_tac >>
  simp[intcall_completed_def] >> disch_then drule >> strip_tac >>
  qexistsl_tac [`p`,`sz`] >> simp[] >>
  irule intcall_local_value_transport >> metis_tac[]
QED

Theorem intcall_pending_transport:
  intcall_pending env ce caps G tn s /\
  (!op. MEM op (MAP (SND o SND) caps) ==>
    eval_operand op t = eval_operand op s /\
    op_taint un op = op_taint tn op /\
    (!p. op = Var p ==> FLOOKUP H p = FLOOKUP G p)) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!a. a < s.vs_alloca_next ==>
    mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory) /\
  (!a. a < s.vs_alloca_next /\ a IN un.t_mem ==> a IN tn.t_mem) ==>
  intcall_pending env ce caps H un t
Proof
  strip_tac >> simp[intcall_pending_def, EVERY_MEM] >>
  gen_tac >> strip_tac >> PairCases_on `e` >> gvs[] >>
  qpat_x_assum `intcall_pending _ _ _ _ _ _` mp_tac >>
  simp[intcall_pending_def, EVERY_MEM] >>
  disch_then (qspec_then `(e0,e1,e2)` mp_tac) >> simp[] >> strip_tac >>
  `MEM e2 (MAP (SND o SND) caps)` by
    (simp[MEM_MAP] >> qexists_tac `(e0,e1,e2)` >> simp[]) >>
  qpat_x_assum `!op. MEM op _ ==> _` drule >> strip_tac >>
  qexistsl_tac [`entry`,`off`,`sz`,`w`] >> simp[] >>
  Cases_on `e1` >> gvs[] >>
  irule intcall_local_value_transport >>
  gvs[eval_operand_def] >> metis_tac[]
QED
