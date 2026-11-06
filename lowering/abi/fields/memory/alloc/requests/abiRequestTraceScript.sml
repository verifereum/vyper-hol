(* TOP-LEVEL: traces of actual heterogeneous requests compose and preserve
   a concrete reservation. Only allocator fields are observed, so ordinary
   expression writes and SSA updates remain independent of this resource proof. *)
Theory abiRequestTrace
Ancestors
  abiRequestProfile abiAllocationSequence abiAllocationSequenceFields
  abiAllocatorState abiAllocationTrace memoryValueSnapshot venomState list pair

Definition abi_request_trace_def:
  abi_request_trace requests before after <=>
    ?executed. EVERY (\request. MEM request requests) executed /\
      abi_allocator_state after = abi_allocator_state (abi_allocation_sequence executed before)
End

Theorem abi_request_trace_identity:
  !requests before after.
    abi_allocator_state after = abi_allocator_state before ==> abi_request_trace requests before after
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [abi_request_trace_def] >> qexists_tac `[]` >> simp[]
QED

Theorem abi_request_trace_frame:
  !requests id byte_count before after.
    MEM (id,byte_count) requests /\
    abi_allocator_state after = abi_allocator_state (memory_snapshot_alloc_frame id byte_count before) ==>
    abi_request_trace requests before after
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_request_trace_def] >>
  qexists_tac `[(id,byte_count)]` >> simp[]
QED

Theorem abi_request_trace_trans:
  !requests before middle after.
    abi_request_trace requests before middle /\ abi_request_trace requests middle after ==>
    abi_request_trace requests before after
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_request_trace_def] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `left` strip_assume_tac)
    (qx_choose_then `right` strip_assume_tac)) >>
  qexists_tac `left ++ right` >> simp[abi_allocation_sequence_append] >>
  qspecl_then [`right`, `abi_allocation_sequence left before`, `middle`] mp_tac abi_allocator_state_sequence >> simp[]
QED

Theorem abi_request_trace_fields:
  !requests before after before' after'.
    abi_request_trace requests before after /\
    abi_allocator_state before' = abi_allocator_state before /\
    abi_allocator_state after' = abi_allocator_state after ==>
    abi_request_trace requests before' after'
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_request_trace_def] >> rpt strip_tac >>
  rename1 `EVERY (\request. MEM request requests) executed` >> qexists_tac `executed` >> simp[] >>
  qspecl_then [`executed`, `before`, `before'`] mp_tac abi_allocator_state_sequence >> simp[]
QED

Theorem abi_request_reservation_sequence:
  !executed reserved requests ss.
    EVERY (\request. MEM request requests) executed /\ abi_request_reservation reserved requests ss ==>
    abi_request_reservation reserved requests (abi_allocation_sequence executed ss)
Proof
  Induct_on `executed` >- simp[] >> rpt gen_tac >>
  rename1 `EVERY _ (request::rest)` >> Cases_on `request` >>
  simp_tac (srw_ss()) [abi_allocation_sequence_cons] >> strip_tac >>
  first_x_assum irule >> simp[abi_request_reservation_frame]
QED

Theorem abi_request_trace_reservation:
  !requests before after reserved.
    abi_request_trace requests before after /\ abi_request_reservation reserved requests before ==>
    abi_request_reservation reserved requests after
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_request_trace _ _ _` (mp_tac o REWRITE_RULE [abi_request_trace_def]) >>
  disch_then (qx_choose_then `executed` strip_assume_tac) >>
  `abi_request_reservation reserved requests (abi_allocation_sequence executed before)` by
    (irule abi_request_reservation_sequence >> simp[]) >>
  qspecl_then [`reserved`, `requests`, `abi_allocation_sequence executed before`, `after`]
    mp_tac abi_request_reservation_allocator_state >> simp[]
QED

Theorem abi_request_trace_uniform:
  !byte_count ids requests before after.
    abi_allocation_trace byte_count ids before after /\ EVERY (\id. MEM (id,byte_count) requests) ids ==>
    abi_request_trace requests before after
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocation_trace_def, abi_request_trace_def] >> strip_tac >>
  rename1 `EVERY (\id. MEM id ids) executed` >>
  qexists_tac `MAP (\id. (id,byte_count)) executed` >> simp[] >>
  simp_tac (srw_ss()) [EVERY_MAP, EVERY_MEM] >> qx_gen_tac `id` >> DISCH_TAC >>
  `MEM id ids` by fs[EVERY_MEM] >>
  qpat_x_assum `EVERY _ ids` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then (qspec_then `id` mp_tac) >> simp[]
QED
