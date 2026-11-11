(* TOP-LEVEL: the real output allocation preserves compatible encoder
   scratch requests, including cached records and the complete field profile. *)
Theory abiLogAllocationRequests
Ancestors
  abiAllocationFrame abiAllocatedState abiAllocatorState abiFieldRequests
  memoryValueSnapshot venomState list pair arithmetic

Theorem buffer_allocation_request:
  !id var_base capacity index before after request_id request_size.
    after = (memory_snapshot_allocated id var_base capacity before with vs_inst_idx := index) /\
    abi_alloca_request_ok request_id request_size before /\
    (request_id = id ==> request_size <= capacity) ==>
    abi_alloca_request_ok request_id request_size after
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`id`, `capacity`, `before`, `request_id`, `request_size`] abi_allocation_frame_request) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `abi_allocator_state after = abi_allocator_state (memory_snapshot_alloc_frame id capacity before)` by
    simp[memory_snapshot_allocated_def] >>
  drule_all abi_alloca_request_ok_state >> simp[]
QED

Theorem buffer_allocation_word_requests:
  !id var_base capacity index before after requests.
    after = (memory_snapshot_allocated id var_base capacity before with vs_inst_idx := index) /\
    32 <= capacity /\ EVERY (\request. SND request = 32) requests /\
    EVERY (\request. abi_alloca_request_ok (FST request) (SND request) before) requests ==>
    EVERY (\request. abi_alloca_request_ok (FST request) (SND request) after) requests
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [EVERY_MEM] >> qx_gen_tac `request` >> DISCH_TAC >>
  `SND request = 32 /\ abi_alloca_request_ok (FST request) (SND request) before` by fs[EVERY_MEM] >>
  mp_tac (Q.SPECL [`id`, `var_base`, `capacity`, `index`, `before`, `after`,
    `FST (request:num # num)`, `SND (request:num # num)`] buffer_allocation_request) >>
  impl_tac >- simp[] >> simp[]
QED

Theorem abi_log_allocation_scratch_requests:
  !rows id var_base capacity index before after.
    after = (memory_snapshot_allocated id var_base capacity before with vs_inst_idx := index) /\
    32 <= capacity /\ abi_alloca_request_ok (id + 1) 32 before /\
    EVERY (\request. abi_alloca_request_ok (FST request) (SND request) before) (abi_field_requests (id + 3) rows) ==>
    abi_alloca_request_ok (id + 1) 32 after /\
    EVERY (\request. abi_alloca_request_ok (FST request) (SND request) after) (abi_field_requests (id + 3) rows)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (mp_tac (Q.SPECL [`id`, `var_base`, `capacity`, `index`, `before`, `after`, `id + 1`, `32`]
        buffer_allocation_request) >> impl_tac >- simp[] >> simp[]) >>
  mp_tac (Q.SPECL [`id`, `var_base`, `capacity`, `index`, `before`, `after`, `abi_field_requests (id + 3) rows`]
    buffer_allocation_word_requests) >> impl_tac >- simp[abi_field_requests_sizes] >> simp[]
QED
