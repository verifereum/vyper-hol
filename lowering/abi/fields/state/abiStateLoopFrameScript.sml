(* TOP-LEVEL: array counter setup, loop navigation, head/tail updates, and
   both exits preserve the external state carried by the ABI state frame. *)
Theory abiStateLoopFrame
Ancestors
  abiStateFrame abiStateFrameOps abiStaticLoopEntry abiStaticLoopHeader
  abiDynamicLoopEntry abiDynamicLoopHeader abiDynamicLoopBody abiDynamicLoopStep
  abiDynamicLoopLatch abiDynamicLoopUpdate abiDynamicLoopExit abiDynamicLoopFinish
  abiDynArrayEnds abiDynArrayBoundaryFrames venomState list words

Theorem abi_state_context_static_loop_entry[simp]:
  !id var_base ss.
    abi_state_context (abi_static_loop_entry_state id var_base ss) = abi_state_context ss
Proof
  simp[abi_static_loop_entry_state_def]
QED

Theorem abi_state_context_dynamic_loop_entry[simp]:
  !id var_base abi_sz len_word ss.
    abi_state_context (abi_dynamic_loop_entry_state id var_base abi_sz len_word ss) = abi_state_context ss
Proof
  simp[abi_dynamic_loop_entry_state_def, abi_dynamic_loop_entry_tail_state_def, LET_THM]
QED

Theorem abi_state_context_dynamic_loop_child[simp]:
  !var_base labels dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr len_word ss.
    abi_state_context (abi_dynamic_loop_child_state var_base labels dst_addr src_addr abi_sz mem_sz
      counter_addr dyn_addr len_word ss) = abi_state_context ss
Proof
  simp[abi_dynamic_loop_child_state_def, abi_dynamic_loop_body_state_def,
    abi_dynamic_loop_header_state_def, abi_static_loop_header_state_def, LET_THM]
QED

Theorem abi_state_context_dynamic_loop_update[simp]:
  !mid head_addr dyn_addr counter_addr index tail_offset child_size ss.
    abi_state_context (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr
      index tail_offset child_size ss) = abi_state_context ss
Proof
  simp[abi_dynamic_loop_update_state_def, abi_dynamic_loop_latch_state_def]
QED

Theorem abi_state_context_dynamic_loop_finish[simp]:
  !next_var var_base labels src_addr counter_addr dyn_addr len_word ss.
    abi_state_context (abi_dynamic_loop_finish_state next_var var_base labels src_addr counter_addr dyn_addr len_word ss) =
      abi_state_context ss
Proof
  simp[abi_dynamic_loop_finish_state_def, abi_dynamic_loop_exit_state_def,
    abi_dynamic_loop_header_state_def, abi_static_loop_header_state_def, LET_THM]
QED

Theorem abi_state_context_dynarray_entry[simp]:
  !id var_base dst_addr src_addr ss.
    abi_state_context (abi_dynarray_entry_state id var_base dst_addr src_addr ss) = abi_state_context ss
Proof
  simp[abi_dynarray_entry_state_def, LET_THM]
QED

Theorem abi_state_context_dynarray_boundary[simp]:
  !cs dst_addr src_addr ss.
    abi_state_context (abi_dynarray_entry_boundary cs dst_addr src_addr ss) = abi_state_context ss
Proof
  simp[abi_dynarray_entry_boundary_def]
QED

Theorem abi_state_context_dynarray_exit[simp]:
  !var_base parent_addr encoded_word ss.
    abi_state_context (abi_dynarray_exit_state var_base parent_addr encoded_word ss) = abi_state_context ss
Proof
  simp[abi_dynarray_exit_state_def, LET_THM]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI loop external-state frames: " ^ name)
  end) (DB.thms "abiStateLoopFrame")
