(* TOP-LEVEL: a sequence of real allocation frames preserves old records,
   bounds its frontier by the request budget, and records each requested
   scratch window. Initial-state premises cover fresh and reused slots. *)
Theory abiAllocationSequence
Ancestors
  abiAllocationFrame memoryValueSnapshot venomMemDefs venomState
  finite_map list rich_list pair words arithmetic

Definition abi_allocation_sequence_def:
  abi_allocation_sequence allocations ss =
    FOLDL (\st allocation. memory_snapshot_alloc_frame (FST allocation) (SND allocation) st) ss allocations
End

Theorem abi_allocation_sequence_nil[simp]:
  !ss. abi_allocation_sequence [] ss = ss
Proof
  simp[abi_allocation_sequence_def]
QED

Theorem abi_allocation_sequence_cons[simp]:
  !allocation allocations ss.
    abi_allocation_sequence (allocation::allocations) ss =
      abi_allocation_sequence allocations (memory_snapshot_alloc_frame (FST allocation) (SND allocation) ss)
Proof
  simp[abi_allocation_sequence_def]
QED

Theorem abi_allocation_sequence_append:
  !left right ss.
    abi_allocation_sequence (left ++ right) ss =
      abi_allocation_sequence right (abi_allocation_sequence left ss)
Proof
  simp[abi_allocation_sequence_def, FOLDL_APPEND]
QED

Theorem abi_allocation_sequence_inv:
  !allocations ss.
    EVERY (\allocation. SND allocation < dimword(:256)) allocations /\ alloca_inv ss ==>
    alloca_inv (abi_allocation_sequence allocations ss)
Proof
  Induct_on `allocations` >- simp[] >>
  qx_gen_tac `allocation` >>
  rpt gen_tac >> simp_tac bool_ss [EVERY_DEF, abi_allocation_sequence_cons] >> strip_tac >>
  first_x_assum irule >> simp[] >> irule abi_allocation_frame_inv >> simp[]
QED

Theorem abi_allocation_sequence_next:
  !allocations ss.
    ss.vs_alloca_next <= (abi_allocation_sequence allocations ss).vs_alloca_next /\
    (abi_allocation_sequence allocations ss).vs_alloca_next <=
      ss.vs_alloca_next + SUM (MAP SND allocations)
Proof
  Induct_on `allocations` >- simp[] >>
  qx_gen_tac `allocation` >> rpt gen_tac >>
  first_x_assum (qspec_then `memory_snapshot_alloc_frame (FST allocation) (SND allocation) ss` strip_assume_tac) >>
  mp_tac (Q.SPECL [`FST (allocation:num # num)`, `SND (allocation:num # num)`, `ss`]
    abi_allocation_frame_next) >> strip_tac >>
  simp_tac bool_ss [abi_allocation_sequence_cons, MAP, SUM] >> decide_tac
QED

Theorem abi_allocation_sequence_lookup_old:
  !allocations ss other offset recorded_size.
    FLOOKUP ss.vs_allocas other = SOME (offset,recorded_size) ==>
    FLOOKUP (abi_allocation_sequence allocations ss).vs_allocas other = SOME (offset,recorded_size)
Proof
  Induct_on `allocations` >- simp[] >>
  qx_gen_tac `allocation` >>
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [abi_allocation_sequence_cons] >>
  first_x_assum irule >> irule abi_allocation_frame_lookup_old >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_allocation_sequence_lookup_other:
  !allocations ss other.
    EVERY (\allocation. FST allocation <> other) allocations ==>
    FLOOKUP (abi_allocation_sequence allocations ss).vs_allocas other = FLOOKUP ss.vs_allocas other
Proof
  Induct_on `allocations` >- simp[] >>
  qx_gen_tac `allocation` >>
  rpt gen_tac >> simp_tac bool_ss [EVERY_DEF, abi_allocation_sequence_cons] >> strip_tac >>
  first_x_assum (qspecl_then [`memory_snapshot_alloc_frame (FST allocation) (SND allocation) ss`, `other`] mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  mp_tac (Q.SPECL [`FST (allocation:num # num)`, `SND (allocation:num # num)`, `ss`, `other`]
    abi_allocation_frame_lookup_other) >>
  impl_tac >- simp[] >> simp[]
QED

Theorem abi_allocation_sequence_record:
  !prefix id byte_count suffix ss.
    alloca_inv ss /\ EVERY (\allocation. SND allocation < dimword(:256)) prefix /\
    EVERY (\allocation. FST allocation <> id) prefix /\ abi_alloca_request_ok id byte_count ss /\
    ss.vs_alloca_next + SUM (MAP SND prefix) + byte_count < dimword(:256) ==>
    ?offset recorded_size.
      FLOOKUP (abi_allocation_sequence (prefix ++ [(id,byte_count)] ++ suffix) ss).vs_allocas id =
        SOME (offset,recorded_size) /\
      byte_count <= recorded_size /\
      w2n (memory_snapshot_addr id (abi_allocation_sequence prefix ss)) = offset
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`prefix`, `ss`, `id`] abi_allocation_sequence_lookup_other) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  `abi_alloca_request_ok id byte_count (abi_allocation_sequence prefix ss)` by
    fs[abi_alloca_request_ok_def] >>
  `alloca_inv (abi_allocation_sequence prefix ss)` by (irule abi_allocation_sequence_inv >> simp[]) >>
  mp_tac (Q.SPECL [`prefix`, `ss`] abi_allocation_sequence_next) >> strip_tac >>
  `((abi_allocation_sequence prefix ss).vs_alloca_next + byte_count) < dimword(:256)` by decide_tac >>
  mp_tac (Q.SPECL [`id`, `byte_count`, `abi_allocation_sequence prefix ss`] abi_allocation_frame_record) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `offset` (qx_choose_then `recorded_size` strip_assume_tac)) >>
  qexistsl_tac [`offset`, `recorded_size`] >>
  asm_simp_tac bool_ss [abi_allocation_sequence_append, abi_allocation_sequence_cons, abi_allocation_sequence_nil,
    FST, SND] >>
  irule abi_allocation_sequence_lookup_old >> first_assum MATCH_ACCEPT_TAC
QED
