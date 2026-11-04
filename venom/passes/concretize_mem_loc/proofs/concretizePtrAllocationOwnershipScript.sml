Theory concretizePtrAllocationOwnership
Ancestors concretizePtrAllocationOrigins venomExecSemantics venomState
  venomInst finite_map words list

Definition ptr_alloc_table_ok_def:
  ptr_alloc_table_ok s <=>
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
      b + sz <= s.vs_alloca_next) /\
    (!aid aid' b sz b' sz' x.
      FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      FLOOKUP s.vs_allocas aid' = SOME (b',sz') /\
      b <= x /\ x < b + sz /\ b' <= x /\ x < b' + sz' ==> aid = aid')
End

Definition ptr_alloc_floor_def:
  ptr_alloc_floor q s <=>
    !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> q <= b
End

Definition ptr_active_alloc_geometry_def:
  (ptr_active_alloc_geometry [] <=> T) /\
  (ptr_active_alloc_geometry (s::ss) <=>
    ptr_alloc_table_ok s /\ ptr_active_alloc_geometry ss /\
    case ss of [] => T | p::ps =>
      p.vs_alloca_next <= s.vs_alloca_next /\ ptr_alloc_floor p.vs_alloca_next s)
End

Theorem ptr_active_alloc_geometry_nil[simp]:
  ptr_active_alloc_geometry []
Proof
  simp[ptr_active_alloc_geometry_def]
QED

Theorem ptr_active_alloc_geometry_singleton[simp]:
  ptr_active_alloc_geometry [s] <=> ptr_alloc_table_ok s
Proof
  simp[ptr_active_alloc_geometry_def]
QED

Theorem ptr_alloc_empty:
  s.vs_allocas = FEMPTY ==> ptr_alloc_table_ok s /\ ptr_alloc_floor q s
Proof
  simp[ptr_alloc_table_ok_def, ptr_alloc_floor_def]
QED

Theorem ptr_exec_alloca_table_ok:
  ptr_alloc_table_ok s /\ exec_alloca inst s n = OK s' ==>
  ptr_alloc_table_ok s'
Proof
  rw[exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def, ptr_alloc_table_ok_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  Cases_on `inst.inst_id = aid` >> Cases_on `inst.inst_id = aid'` >> gvs[] >>
  qpat_assum `!aid b sz. FLOOKUP _ _ = _ ==> _`
    (fn th => imp_res_tac th) >> gvs[] >> metis_tac[]
QED

Theorem ptr_exec_alloca_floor:
  ptr_alloc_floor q s /\ q <= s.vs_alloca_next /\ exec_alloca inst s n = OK s' ==>
  ptr_alloc_floor q s' /\ q <= s'.vs_alloca_next
Proof
  rw[exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def, ptr_alloc_floor_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `inst.inst_id = aid` >> gvs[] >> metis_tac[]
QED

Theorem ptr_exec_alloca_fresh_disjoint:
  ptr_alloc_table_ok s /\ exec_alloca inst s n = OK s' /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ b <= x /\ x < b + sz ==>
  ~(s.vs_alloca_next <= x /\ x < s.vs_alloca_next + w2n n)
Proof
  simp[ptr_alloc_table_ok_def] >> rpt strip_tac >>
  `b + sz <= s.vs_alloca_next` by metis_tac[] >> decide_tac
QED
