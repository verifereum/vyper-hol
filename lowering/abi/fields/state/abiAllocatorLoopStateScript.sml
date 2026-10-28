(* TOP-LEVEL: the byte-array body and both exits do not allocate. The only
   allocator changes come from the explicit counter setup before the loop. *)
Theory abiAllocatorLoopState
Ancestors
  abiAllocatorState abiDynamicLoopStep abiDynamicLoopBody abiDynamicLoopHeader
  abiStaticLoopHeader abiDynamicLoopUpdate abiDynamicLoopLatch
  abiDynamicLoopFinish abiDynamicLoopExit abiDynArrayEnds
  venomState list words

Theorem abi_allocator_state_dynamic_child[simp]:
  !var_base labels dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr len_word ss.
    abi_allocator_state (abi_dynamic_loop_child_state var_base labels dst_addr src_addr abi_sz mem_sz
      counter_addr dyn_addr len_word ss) = abi_allocator_state ss
Proof
  simp[abi_dynamic_loop_child_state_def, abi_dynamic_loop_body_state_def,
    abi_dynamic_loop_header_state_def, abi_static_loop_header_state_def, LET_THM]
QED

Theorem abi_allocator_state_dynamic_update[simp]:
  !mid head_addr dyn_addr counter_addr index tail_offset child_size ss.
    abi_allocator_state (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr
      index tail_offset child_size ss) = abi_allocator_state ss
Proof
  simp[abi_dynamic_loop_update_state_def, abi_dynamic_loop_latch_state_def]
QED

Theorem abi_allocator_state_dynamic_finish[simp]:
  !next_var var_base labels src_addr counter_addr dyn_addr len_word ss.
    abi_allocator_state (abi_dynamic_loop_finish_state next_var var_base labels src_addr counter_addr dyn_addr len_word ss) =
      abi_allocator_state ss
Proof
  simp[abi_dynamic_loop_finish_state_def, abi_dynamic_loop_exit_state_def,
    abi_dynamic_loop_header_state_def, abi_static_loop_header_state_def, LET_THM]
QED

Theorem abi_allocator_state_dynarray_exit[simp]:
  !var_base parent_addr encoded_word ss.
    abi_allocator_state (abi_dynarray_exit_state var_base parent_addr encoded_word ss) = abi_allocator_state ss
Proof
  simp[abi_dynarray_exit_state_def, LET_THM]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed allocation-free ABI loop phases: " ^ name)
  end) (DB.thms "abiAllocatorLoopState")
