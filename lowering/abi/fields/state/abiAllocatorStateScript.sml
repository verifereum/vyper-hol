(* TOP-LEVEL: allocator observations and their preservation by instructions
   that change registers, memory, or control position without allocating. *)
Theory abiAllocatorState
Ancestors
  abiAllocationSequenceFields abiAllocationSequence abiBytestringExec
  abiChildPrefix abiChildSuffix abiFieldAddress
  venomState venomExecSemantics list words

Definition abi_allocator_state_def:
  abi_allocator_state ss = (ss.vs_allocas,ss.vs_alloca_next)
End

Theorem abi_allocator_state_eq:
  !before after.
    (abi_allocator_state after = abi_allocator_state before) <=>
    after.vs_allocas = before.vs_allocas /\ after.vs_alloca_next = before.vs_alloca_next
Proof
  simp[abi_allocator_state_def]
QED

Theorem abi_allocator_state_mutable[simp]:
  !ss vars mem prev bb index.
    abi_allocator_state (ss with vs_vars := vars) = abi_allocator_state ss /\
    abi_allocator_state (ss with vs_memory := mem) = abi_allocator_state ss /\
    abi_allocator_state (ss with vs_prev_bb := prev) = abi_allocator_state ss /\
    abi_allocator_state (ss with vs_current_bb := bb) = abi_allocator_state ss /\
    abi_allocator_state (ss with vs_inst_idx := index) = abi_allocator_state ss
Proof
  simp[abi_allocator_state_def]
QED

Theorem abi_allocator_state_primitives[simp]:
  !ss name value offset bytes src count label.
    abi_allocator_state (update_var name value ss) = abi_allocator_state ss /\
    abi_allocator_state (mstore offset value ss) = abi_allocator_state ss /\
    abi_allocator_state (write_memory_with_expansion offset bytes ss) = abi_allocator_state ss /\
    abi_allocator_state (mcopy offset src count ss) = abi_allocator_state ss /\
    abi_allocator_state (jump_to label ss) = abi_allocator_state ss
Proof
  simp[abi_allocator_state_def, update_var_def, mstore_def,
    write_memory_with_expansion_def, mcopy_def, jump_to_def, LET_THM]
QED

Theorem abi_allocator_state_bytestring[simp]:
  !dst_addr src_addr ss.
    abi_allocator_state (bytestring_copy_state dst_addr src_addr ss) = abi_allocator_state ss
Proof
  simp[bytestring_copy_state_def, LET_THM]
QED

Theorem abi_allocator_state_child_prefix[simp]:
  !var_base head_offset dst_addr dyn_addr ss.
    abi_allocator_state (abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss) = abi_allocator_state ss
Proof
  simp[abi_child_prefix_state_def]
QED

Theorem abi_allocator_state_child_suffix[simp]:
  !var_base head_addr dyn_addr tail_offset child_len ss.
    abi_allocator_state (abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss) = abi_allocator_state ss
Proof
  simp[abi_child_suffix_state_def]
QED

Theorem abi_allocator_state_field_address[simp]:
  !cs offset root_addr ss.
    abi_allocator_state (abi_field_address_state cs offset root_addr ss) = abi_allocator_state ss
Proof
  simp[abi_field_address_state_def]
QED

Theorem abi_allocator_state_sequence:
  !allocations before after.
    abi_allocator_state after = abi_allocator_state before ==>
    abi_allocator_state (abi_allocation_sequence allocations after) =
      abi_allocator_state (abi_allocation_sequence allocations before)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocator_state_eq] >> strip_tac >>
  irule abi_allocation_sequence_fields >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed allocator-state observation: " ^ name)
  end) (DB.thms "abiAllocatorState")
