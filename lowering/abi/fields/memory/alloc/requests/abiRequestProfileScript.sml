(* TOP-LEVEL: a finite request profile preserves compatible cached slots
   and enough reserved space through each actual heterogeneous allocation.
   Repeated identities are allowed when their requested sizes agree. *)
Theory abiRequestProfile
Ancestors
  abiAllocationBudgetBounds abiAllocationBudget abiAllocationFrame abiAllocatorState
  memoryValueSnapshot venomState finite_map list pair words arithmetic

Definition abi_requests_consistent_def:
  abi_requests_consistent requests <=>
    !id left right. MEM (id,left) requests /\ MEM (id,right) requests ==> left = right
End

Definition abi_requests_compatible_def:
  abi_requests_compatible requests ss <=>
    EVERY (\request. abi_alloca_request_ok (FST request) (SND request) ss) requests
End

Definition abi_request_reservation_def:
  abi_request_reservation reserved requests ss <=>
    abi_requests_consistent requests /\ EVERY (\request. SND request <= reserved) requests /\
    abi_requests_compatible requests ss /\
    abi_alloca_budget reserved (MAP FST requests) ss + reserved < dimword(:256)
End

Theorem abi_requests_compatible_member:
  !requests ss id byte_count.
    abi_requests_compatible requests ss /\ MEM (id,byte_count) requests ==>
    abi_alloca_request_ok id byte_count ss
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_requests_compatible _ _`
    (mp_tac o REWRITE_RULE [abi_requests_compatible_def, EVERY_MEM]) >>
  disch_then (qspec_then `(id,byte_count)` mp_tac) >> simp[]
QED

Theorem abi_requests_compatible_frame:
  !requests id byte_count ss.
    abi_requests_consistent requests /\ MEM (id,byte_count) requests /\ abi_requests_compatible requests ss ==>
    abi_requests_compatible requests (memory_snapshot_alloc_frame id byte_count ss)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_requests_compatible_def, EVERY_MEM] >>
  qx_gen_tac `request` >> DISCH_TAC >> Cases_on `request` >> simp_tac bool_ss [FST, SND] >>
  rename1 `abi_alloca_request_ok other requested (memory_snapshot_alloc_frame id byte_count ss)` >>
  `abi_alloca_request_ok other requested ss` by (drule_all abi_requests_compatible_member >> simp[]) >>
  `other = id ==> requested <= byte_count` by
    (DISCH_TAC >> gvs[] >>
     qpat_x_assum `abi_requests_consistent _` (mp_tac o REWRITE_RULE [abi_requests_consistent_def]) >>
     disch_then (qspecl_then [`id`, `requested`, `byte_count`] mp_tac) >> simp[]) >>
  qspecl_then [`id`, `byte_count`, `ss`, `other`, `requested`] mp_tac abi_allocation_frame_request >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem abi_request_reservation_frame:
  !reserved requests id byte_count ss.
    abi_request_reservation reserved requests ss /\ MEM (id,byte_count) requests ==>
    abi_request_reservation reserved requests (memory_snapshot_alloc_frame id byte_count ss)
Proof
  rpt gen_tac >> strip_tac >> fs[abi_request_reservation_def] >>
  `byte_count <= reserved` by
    (qpat_x_assum `EVERY (\request. SND request <= reserved) requests`
      (mp_tac o REWRITE_RULE [EVERY_MEM]) >> disch_then (qspec_then `(id,byte_count)` mp_tac) >> simp[]) >>
  `MEM id (MAP FST requests)` by (simp[MEM_MAP] >> qexists_tac `(id,byte_count)` >> simp[]) >>
  qspecl_then [`reserved`, `MAP FST requests`, `id`, `byte_count`, `ss`]
    mp_tac abi_alloca_budget_frame_bound >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `abi_requests_compatible requests (memory_snapshot_alloc_frame id byte_count ss)` by
    (drule_all abi_requests_compatible_frame >> simp[]) >>
  simp_tac bool_ss [abi_request_reservation_def] >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

Theorem abi_request_reservation_room:
  !reserved requests id byte_count ss.
    abi_request_reservation reserved requests ss /\ MEM (id,byte_count) requests ==>
    byte_count < dimword(:256) /\ ss.vs_alloca_next + byte_count < dimword(:256) /\
    abi_alloca_request_ok id byte_count ss
Proof
  rpt gen_tac >> strip_tac >> fs[abi_request_reservation_def] >>
  `byte_count <= reserved` by
    (qpat_x_assum `EVERY (\request. SND request <= reserved) requests`
      (mp_tac o REWRITE_RULE [EVERY_MEM]) >> disch_then (qspec_then `(id,byte_count)` mp_tac) >> simp[]) >>
  qspecl_then [`reserved`, `MAP FST requests`, `ss`, `byte_count`] mp_tac abi_alloca_budget_request_room >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]) >> DISCH_TAC >>
  `abi_alloca_request_ok id byte_count ss` by (drule_all abi_requests_compatible_member >> simp[]) >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

Theorem abi_request_reservation_allocator_state:
  !reserved requests before after.
    abi_allocator_state after = abi_allocator_state before ==>
    (abi_request_reservation reserved requests after <=> abi_request_reservation reserved requests before)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocator_state_eq] >> strip_tac >>
  simp[abi_request_reservation_def, abi_requests_compatible_def, abi_alloca_request_ok_def,
    abi_alloca_budget_def, abi_alloca_pending_def]
QED
