(* TOP-LEVEL: compiler allocation identities at or beyond a fresh boundary
   are absent. Allocation sequences retain freshness above their request IDs. *)
Theory abiAllocationFresh
Ancestors
  abiAllocatorState abiAllocatedWindows abiAllocationSequence abiAllocationFrame
  venomState finite_map list arithmetic

Definition abi_allocation_fresh_def:
  abi_allocation_fresh next_id ss <=> !id. next_id <= id ==> FLOOKUP ss.vs_allocas id = NONE
End

Theorem abi_allocation_fresh_mono:
  !next_id later_id ss.
    abi_allocation_fresh next_id ss /\ next_id <= later_id ==> abi_allocation_fresh later_id ss
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocation_fresh_def] >> strip_tac >>
  qx_gen_tac `id` >> DISCH_TAC >> first_x_assum irule >> decide_tac
QED

Theorem abi_allocation_fresh_state:
  !before after next_id.
    abi_allocator_state after = abi_allocator_state before ==>
    (abi_allocation_fresh next_id after = abi_allocation_fresh next_id before)
Proof
  simp[abi_allocator_state_eq, abi_allocation_fresh_def]
QED

Theorem abi_allocation_fresh_allocated_id:
  !next_id ss id offset byte_count.
    abi_allocation_fresh next_id ss /\ abi_allocated_window ss id offset byte_count ==> id < next_id
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocation_fresh_def, abi_allocated_window_def] >> strip_tac >>
  Cases_on `next_id <= id` >- (first_x_assum drule >> simp[]) >> decide_tac
QED

Theorem abi_allocation_fresh_request:
  !next_id ss id byte_count.
    abi_allocation_fresh next_id ss /\ next_id <= id ==> abi_alloca_request_ok id byte_count ss
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocation_fresh_def, abi_alloca_request_ok_def] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem abi_allocation_fresh_sequence:
  !allocations next_id later_id ss.
    abi_allocation_fresh next_id ss /\ next_id <= later_id /\
    EVERY (\allocation. FST allocation < later_id) allocations ==>
    abi_allocation_fresh later_id (abi_allocation_sequence allocations ss)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_allocation_fresh_def] >> qx_gen_tac `id` >> DISCH_TAC >>
  `EVERY (\allocation. FST allocation <> id) allocations` by
    (simp_tac bool_ss [EVERY_MEM] >> qx_gen_tac `allocation` >> DISCH_TAC >>
     `FST allocation < later_id` by fs[EVERY_MEM] >> decide_tac) >>
  drule_all abi_allocation_sequence_lookup_other >> DISCH_TAC >>
  `next_id <= id` by decide_tac >> fs[abi_allocation_fresh_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed compiler allocation freshness: " ^ name)
  end) (DB.thms "abiAllocationFresh")
