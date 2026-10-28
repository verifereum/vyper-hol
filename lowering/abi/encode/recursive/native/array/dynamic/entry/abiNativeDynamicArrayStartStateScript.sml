(* TOP-LEVEL: actual dynamic-array setup allocates or reuses its index and
   tail cells, initializes them and jumps to the generated header. Its
   trace records exactly those two requests; earlier operands survive. *)
Theory abiNativeDynamicArrayStartState
Ancestors
  abiDynamicLoopEntry abiDynamicLoopEntryFrames abiDynamicLoopCode abiStaticLoopEntry abiStaticLoopBody abiStaticLoopCode
  abiDynBytesAllocState abiStateLoopFrame abiStateFrame abiAllocatorState abiAllocationTrace abiAllocationSequence
  abiAllocationFrame abiMemoryFrame abiFieldOperands memoryValueSnapshot compileEnv fragExec venomMemDefs venomState list words arithmetic

Definition abi_native_dynamic_array_start_state_def:
  abi_native_dynamic_array_start_state cs width length_word ss =
    jump_to (fresh_label_output "enc_dyn_hdr" cs.cs_next_label)
      (abi_dynamic_loop_entry_state cs.cs_next_id cs.cs_next_var width length_word ss)
End

Definition abi_native_dynamic_array_tail_addr_def:
  abi_native_dynamic_array_tail_addr cs ss =
    abi_static_loop_counter_addr (cs.cs_next_id + 2) (abi_static_loop_entry_state cs.cs_next_id cs.cs_next_var ss)
End

Theorem abi_native_dynamic_array_start_allocator:
  !cs width length_word ss.
    abi_allocator_state (abi_native_dynamic_array_start_state cs width length_word ss) =
    abi_allocator_state (abi_allocation_sequence [(cs.cs_next_id,32);(cs.cs_next_id + 2,32)] ss)
Proof
  rpt gen_tac >>
  qspecl_then [`memory_snapshot_alloc_frame cs.cs_next_id 32 ss`,
    `abi_static_loop_entry_state cs.cs_next_id cs.cs_next_var ss`, `cs.cs_next_id + 2`, `32`]
    mp_tac abi_allocation_frame_fields >> impl_tac >- simp[abi_static_loop_entry_allocation_fields] >> strip_tac >>
  simp[abi_native_dynamic_array_start_state_def, abi_dynamic_loop_entry_state_def, abi_dynamic_loop_entry_tail_state_def,
    LET_THM, abi_static_loop_alloc_frame_snapshot] >> simp[abi_allocator_state_def]
QED

Theorem abi_native_dynamic_array_start_trace:
  !cs width length_word ids ss.
    MEM cs.cs_next_id ids /\ MEM (cs.cs_next_id + 2) ids ==>
    abi_allocation_trace 32 ids ss (abi_native_dynamic_array_start_state cs width length_word ss)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_allocation_trace_def] >>
  qexists_tac `[cs.cs_next_id;cs.cs_next_id + 2]` >> simp[abi_native_dynamic_array_start_allocator]
QED

Theorem abi_native_dynamic_array_start_frame:
  !cs width length_word ss.
    abi_state_frame ss (abi_native_dynamic_array_start_state cs width length_word ss) /\
    abi_memory_frame [(w2n (abi_static_loop_counter_addr cs.cs_next_id ss),32);
      (w2n (abi_native_dynamic_array_tail_addr cs ss),32)] ss (abi_native_dynamic_array_start_state cs width length_word ss)
Proof
  rpt gen_tac >>
  qspecl_then [`cs.cs_next_id`, `cs.cs_next_var`, `width`, `length_word`, `ss`]
    mp_tac abi_dynamic_loop_entry_memory_frame >>
  simp[abi_native_dynamic_array_start_state_def, abi_native_dynamic_array_tail_addr_def,
    abi_state_frame_def, abi_memory_frame_def, read_memory_def, jump_to_def]
QED

Theorem abi_native_dynamic_array_start_control:
  !cs width length_word ss.
    (abi_native_dynamic_array_start_state cs width length_word ss).vs_current_bb = fresh_label_output "enc_dyn_hdr" cs.cs_next_label /\
    (abi_native_dynamic_array_start_state cs width length_word ss).vs_inst_idx = 0 /\
    (abi_native_dynamic_array_start_state cs width length_word ss).vs_halted = ss.vs_halted
Proof
  simp[abi_native_dynamic_array_start_state_def, jump_to_def, abi_dynamic_loop_entry_control]
QED

Theorem abi_native_dynamic_array_start_old_operand:
  !cs width length_word ss arg_op.
    abi_operand_before cs.cs_next_var arg_op ==>
    eval_operand arg_op (abi_native_dynamic_array_start_state cs width length_word ss) = eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [abi_native_dynamic_array_start_state_def, eval_operand_jump_to_eq] >>
  irule abi_dynamic_loop_entry_operand_frame >>
  qpat_x_assum `abi_operand_before _ _` (mp_tac o PURE_REWRITE_RULE [abi_operand_before_def]) >> DISCH_TAC >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [compiler_var_name_def, ADD_0]) >>
  simp_tac bool_ss [compiler_var_name_def] >> rpt conj_tac >> first_x_assum irule >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array two-allocation setup state: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayStartState")
