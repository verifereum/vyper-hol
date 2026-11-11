(* TOP-LEVEL: allocation frames preserve old records and the allocator
   invariant. A request may be fresh or reuse a sufficiently large record.
   Helpers expose the frontier bound and unchanged allocation fields. *)
Theory abiAllocationFrame
Ancestors
  memoryValueSnapshot localPtrsProps dynCopyExec compileEnv
  venomMemDefs venomExecSemantics venomState venomInst finite_map words arithmetic

Definition abi_alloca_request_ok_def:
  abi_alloca_request_ok id byte_count ss <=>
    !offset recorded_size. FLOOKUP ss.vs_allocas id = SOME (offset,recorded_size) ==>
      byte_count <= recorded_size
End

Theorem abi_allocation_frame_next:
  !id byte_count ss.
    ss.vs_alloca_next <= (memory_snapshot_alloc_frame id byte_count ss).vs_alloca_next /\
    (memory_snapshot_alloc_frame id byte_count ss).vs_alloca_next <= ss.vs_alloca_next + byte_count
Proof
  rpt gen_tac >> simp[memory_snapshot_alloc_frame_def] >> rw[]
QED

Theorem abi_allocation_frame_lookup_other:
  !id byte_count ss other.
    other <> id ==>
    FLOOKUP (memory_snapshot_alloc_frame id byte_count ss).vs_allocas other = FLOOKUP ss.vs_allocas other
Proof
  rpt gen_tac >> DISCH_TAC >> rw[memory_snapshot_alloc_frame_def] >> simp[FLOOKUP_UPDATE]
QED

Theorem abi_allocation_frame_lookup_old:
  !id byte_count ss other offset recorded_size.
    FLOOKUP ss.vs_allocas other = SOME (offset,recorded_size) ==>
    FLOOKUP (memory_snapshot_alloc_frame id byte_count ss).vs_allocas other = SOME (offset,recorded_size)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `other = id` >>
  fs[memory_snapshot_alloc_frame_def, FLOOKUP_UPDATE] >> rw[] >> gvs[FLOOKUP_UPDATE]
QED

Theorem abi_allocation_frame_request:
  !id byte_count ss other requested_size.
    abi_alloca_request_ok other requested_size ss /\ (other = id ==> requested_size <= byte_count) ==>
    abi_alloca_request_ok other requested_size (memory_snapshot_alloc_frame id byte_count ss)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_alloca_request_ok_def] >> strip_tac >>
  Cases_on `other = id` >> gvs[memory_snapshot_alloc_frame_def, FLOOKUP_UPDATE] >>
  rw[] >> gvs[FLOOKUP_UPDATE]
QED

Theorem abi_allocation_fields_inv:
  !before after.
    after.vs_allocas = before.vs_allocas /\ after.vs_alloca_next = before.vs_alloca_next /\ alloca_inv before ==>
    alloca_inv after
Proof
  rpt gen_tac >> strip_tac >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_allocation_frame_inv:
  !id byte_count ss.
    byte_count < dimword(:256) /\ alloca_inv ss ==>
    alloca_inv (memory_snapshot_alloc_frame id byte_count ss)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`id`, `0`, `byte_count`, `ss`] memory_snapshot_allocation_step) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  simp_tac (srw_ss()) [Once step_inst_base_def, mk_inst_def, eval_operand_def] >> DISCH_TAC >>
  drule_all alloca_inv_exec_alloca >> DISCH_TAC >>
  mp_tac (Q.SPECL [`memory_snapshot_allocated id 0 byte_count ss`,
    `memory_snapshot_alloc_frame id byte_count ss`] abi_allocation_fields_inv) >>
  impl_tac >- simp[memory_snapshot_allocated_def, update_var_def] >> simp[]
QED

Theorem abi_allocation_frame_record:
  !id byte_count ss.
    abi_alloca_request_ok id byte_count ss /\ alloca_inv ss /\
    ss.vs_alloca_next + byte_count < dimword(:256) ==>
    ?offset recorded_size.
      FLOOKUP (memory_snapshot_alloc_frame id byte_count ss).vs_allocas id = SOME (offset,recorded_size) /\
      byte_count <= recorded_size /\ w2n (memory_snapshot_addr id ss) = offset /\
      offset + recorded_size <= (memory_snapshot_alloc_frame id byte_count ss).vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP ss.vs_allocas id`
  >- (qexistsl_tac [`ss.vs_alloca_next`, `byte_count`] >>
      simp[memory_snapshot_alloc_frame_def, memory_snapshot_addr_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP ss.vs_allocas id = SOME recorded_region` >> PairCases_on `recorded_region` >>
  rename1 `FLOOKUP ss.vs_allocas id = SOME (offset,recorded_size)` >>
  `offset + recorded_size <= ss.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> first_x_assum drule >> simp[]) >>
  `offset < dimword(:256)` by decide_tac >>
  qexistsl_tac [`offset`, `recorded_size`] >>
  fs[abi_alloca_request_ok_def, memory_snapshot_alloc_frame_def, memory_snapshot_addr_def]
QED

Theorem abi_allocation_frame_fields:
  !before after id byte_count.
    after.vs_allocas = before.vs_allocas /\ after.vs_alloca_next = before.vs_alloca_next ==>
    (memory_snapshot_alloc_frame id byte_count after).vs_allocas =
      (memory_snapshot_alloc_frame id byte_count before).vs_allocas /\
    (memory_snapshot_alloc_frame id byte_count after).vs_alloca_next =
      (memory_snapshot_alloc_frame id byte_count before).vs_alloca_next /\
    memory_snapshot_addr id after = memory_snapshot_addr id before
Proof
  rpt gen_tac >> strip_tac >> simp[memory_snapshot_alloc_frame_def, memory_snapshot_addr_def] >> rw[]
QED
