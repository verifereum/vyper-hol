(* TOP-LEVEL: transfer allocation ownership and request safety across
   register, memory, or control changes with the same allocator state. *)
Theory abiAllocatedState
Ancestors
  abiAllocatorState abiAllocatedWindows abiAllocationFrame venomMemDefs venomState

Theorem abi_allocated_window_state:
  !before after id offset byte_count.
    abi_allocator_state after = abi_allocator_state before ==>
    (abi_allocated_window after id offset byte_count <=> abi_allocated_window before id offset byte_count)
Proof
  simp[abi_allocator_state_eq, abi_allocated_window_def]
QED

Theorem abi_alloca_inv_state:
  !before after.
    abi_allocator_state after = abi_allocator_state before ==> (alloca_inv after <=> alloca_inv before)
Proof
  simp[abi_allocator_state_eq, alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_alloca_request_ok_state:
  !before after id byte_count.
    abi_allocator_state after = abi_allocator_state before ==>
    (abi_alloca_request_ok id byte_count after <=> abi_alloca_request_ok id byte_count before)
Proof
  simp[abi_allocator_state_eq, abi_alloca_request_ok_def]
QED

Theorem abi_allocated_window_field_address[simp]:
  !cs source_offset root_addr ss id offset byte_count.
    abi_allocated_window (abi_field_address_state cs source_offset root_addr ss) id offset byte_count =
      abi_allocated_window ss id offset byte_count
Proof
  rpt gen_tac >> irule abi_allocated_window_state >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed allocation-state ownership transport: " ^ name)
  end) (DB.thms "abiAllocatedState")
