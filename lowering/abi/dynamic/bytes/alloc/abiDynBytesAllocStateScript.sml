(* TOP-LEVEL: the actual parent/index/tail setup has the same allocation
   fields and pointers as three ordinary allocation requests. Memory and
   SSA writes do not change these allocator observations. *)
Theory abiDynBytesAllocState
Ancestors
  abiAllocationFrame abiAllocationSequence memoryValueSnapshot
  abiDynArrayBoundaryFrames abiDynArrayEnds abiStaticLoopEntry dynCopyExec
  compileEnv venomState list pair words arithmetic

Definition abi_dyn_bytes_allocations_def:
  abi_dyn_bytes_allocations cs = [(cs.cs_next_id,32);(cs.cs_next_id + 4,32);(cs.cs_next_id + 6,32)]
End

Definition abi_dyn_bytes_alloc_frame_def:
  abi_dyn_bytes_alloc_frame cs ss = abi_allocation_sequence (abi_dyn_bytes_allocations cs) ss
End

Theorem abi_static_loop_alloc_frame_snapshot:
  !id ss. abi_static_loop_alloc_frame id ss = memory_snapshot_alloc_frame id 32 ss
Proof
  simp[abi_static_loop_alloc_frame_def, memory_snapshot_alloc_frame_def]
QED

Theorem abi_static_loop_counter_snapshot:
  !id ss. abi_static_loop_counter_addr id ss = memory_snapshot_addr id ss
Proof
  simp[abi_static_loop_counter_addr_def, memory_snapshot_addr_def]
QED

Theorem abi_static_loop_entry_allocation_fields:
  !id var_base ss.
    (abi_static_loop_entry_state id var_base ss).vs_allocas = (memory_snapshot_alloc_frame id 32 ss).vs_allocas /\
    (abi_static_loop_entry_state id var_base ss).vs_alloca_next = (memory_snapshot_alloc_frame id 32 ss).vs_alloca_next
Proof
  simp[abi_static_loop_entry_state_def, abi_static_loop_alloc_frame_snapshot, update_var_def]
QED

Theorem abi_dyn_bytes_boundary_allocation_fields:
  !cs dst_addr src_addr ss.
    (abi_dynarray_entry_boundary cs dst_addr src_addr ss).vs_allocas =
      (memory_snapshot_alloc_frame cs.cs_next_id 32 ss).vs_allocas /\
    (abi_dynarray_entry_boundary cs dst_addr src_addr ss).vs_alloca_next =
      (memory_snapshot_alloc_frame cs.cs_next_id 32 ss).vs_alloca_next
Proof
  simp[abi_dynarray_entry_boundary_def, abi_dynarray_entry_state_def, LET_THM,
    update_var_def, abi_static_loop_entry_allocation_fields]
QED

Theorem abi_dyn_bytes_loop_entry_allocation_fields:
  !cs dst_addr src_addr ss.
    (abi_static_loop_entry_state (cs.cs_next_id + 4) (cs.cs_next_var + 2)
      (abi_dynarray_entry_boundary cs dst_addr src_addr ss)).vs_allocas =
      (memory_snapshot_alloc_frame (cs.cs_next_id + 4) 32 (memory_snapshot_alloc_frame cs.cs_next_id 32 ss)).vs_allocas /\
    (abi_static_loop_entry_state (cs.cs_next_id + 4) (cs.cs_next_var + 2)
      (abi_dynarray_entry_boundary cs dst_addr src_addr ss)).vs_alloca_next =
      (memory_snapshot_alloc_frame (cs.cs_next_id + 4) 32 (memory_snapshot_alloc_frame cs.cs_next_id 32 ss)).vs_alloca_next
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`memory_snapshot_alloc_frame cs.cs_next_id 32 ss`,
    `abi_dynarray_entry_boundary cs dst_addr src_addr ss`, `cs.cs_next_id + 4`, `32`]
    abi_allocation_frame_fields) >>
  impl_tac >- simp[abi_dyn_bytes_boundary_allocation_fields] >>
  simp[abi_static_loop_entry_allocation_fields]
QED

Theorem abi_dyn_bytes_allocated_pointers:
  !cs dst_addr src_addr ss.
    abi_static_loop_counter_addr cs.cs_next_id ss = memory_snapshot_addr cs.cs_next_id ss /\
    abi_static_loop_counter_addr (cs.cs_next_id + 4) (abi_dynarray_entry_boundary cs dst_addr src_addr ss) =
      memory_snapshot_addr (cs.cs_next_id + 4) (abi_allocation_sequence [(cs.cs_next_id,32)] ss) /\
    abi_static_loop_counter_addr (cs.cs_next_id + 6)
      (abi_static_loop_entry_state (cs.cs_next_id + 4) (cs.cs_next_var + 2)
        (abi_dynarray_entry_boundary cs dst_addr src_addr ss)) =
      memory_snapshot_addr (cs.cs_next_id + 6)
        (abi_allocation_sequence [(cs.cs_next_id,32);(cs.cs_next_id + 4,32)] ss)
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`cs`, `dst_addr`, `src_addr`, `ss`] abi_dyn_bytes_boundary_allocation_fields) >> strip_tac >>
  mp_tac (Q.SPECL [`cs`, `dst_addr`, `src_addr`, `ss`] abi_dyn_bytes_loop_entry_allocation_fields) >> strip_tac >>
  simp[abi_static_loop_counter_addr_def, memory_snapshot_addr_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic byte/string allocator observations: " ^ name)
  end) (DB.thms "abiDynBytesAllocState")
