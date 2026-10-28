(* TOP-LEVEL: the exact aggregate entry state executes its real prefix,
   initializes the tail cursor and consumes the computed scratch budget.
   Cached replay and fresh allocation share the same allocation trace. *)
Theory abiNativeComplexPrefixState
Ancestors
  abiNativeComplexPrefixCode abiComplexCode abiComplexEntry abiComplexMixedReady abiDynBytesAllocState
  abiBufferBudgetPath abiAllocationTrace abiAllocationSequence abiAllocatorState abiAllocatedWindows
  abiStateFrame abiStateFrameOps abiMemoryFrame abiFieldOperands abiStaticLoopCode
  abiEncoderPathProps memoryValueSnapshot memoryReadProps instIdxIndep compileEnv venomMemDefs venomState list words arithmetic

Definition abi_native_complex_entry_def:
  abi_native_complex_entry head_size cs ss =
    abi_complex_prefix_state cs.cs_next_id cs.cs_next_var head_size ss
      with vs_inst_idx := LENGTH (abi_complex_prefix_cut head_size cs).cs_current_insts
End

Theorem abi_native_complex_entry_context:
  !head_size cs ss.
    (abi_native_complex_entry head_size cs ss).vs_current_bb = ss.vs_current_bb /\
    (abi_native_complex_entry head_size cs ss).vs_inst_idx = LENGTH (abi_complex_prefix_cut head_size cs).cs_current_insts /\
    (abi_native_complex_entry head_size cs ss).vs_halted = ss.vs_halted /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) (abi_native_complex_entry head_size cs ss) =
      SOME (abi_static_loop_counter_addr cs.cs_next_id ss) /\
    mload (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) (abi_native_complex_entry head_size cs ss) = n2w head_size /\
    abi_state_frame ss (abi_native_complex_entry head_size cs ss) /\
    abi_memory_frame [(w2n (abi_static_loop_counter_addr cs.cs_next_id ss),32)] ss
      (abi_native_complex_entry head_size cs ss) /\
    abi_allocator_state (abi_native_complex_entry head_size cs ss) =
      abi_allocator_state (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var 32 ss)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [abi_native_complex_entry_def, eval_op_inst_idx, mload_inst_idx,
    abi_complex_prefix_counter, abi_state_frame_def, abi_complex_prefix_memory_frame] >>
  simp[abi_complex_prefix_state_def, abi_static_loop_alloc_frame_snapshot, memory_snapshot_allocated_def]
QED

Theorem abi_native_complex_entry_old_operand:
  !head_size cs ss arg_op.
    abi_operand_before cs.cs_next_var arg_op ==>
    eval_operand arg_op (abi_native_complex_entry head_size cs ss) = eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [abi_native_complex_entry_def, eval_op_inst_idx] >>
  irule abi_complex_prefix_operand_frame >>
  qpat_x_assum `abi_operand_before _ _` (mp_tac o PURE_REWRITE_RULE [abi_operand_before_def]) >>
  disch_then (qspec_then `cs.cs_next_var` mp_tac) >> simp[]
QED

Theorem abi_native_complex_entry_path:
  !ctx func head_size cs ss.
    fn_has_code cs (abi_complex_prefix_cut head_size cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    fragment_path ctx func ss (abi_native_complex_entry head_size cs ss)
Proof
  simp_tac bool_ss [abi_native_complex_entry_def] >> rpt strip_tac >>
  drule_all abi_complex_prefix_path >> simp[]
QED

Theorem abi_native_complex_entry_allocation:
  !head_size cs ids ss.
    MEM cs.cs_next_id ids /\ abi_alloca_budget 32 ids ss < dimword (:256) /\
    abi_alloca_request_ok cs.cs_next_id 32 ss /\ alloca_inv ss ==>
    abi_allocated_window (abi_native_complex_entry head_size cs ss) cs.cs_next_id
      (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) 32 /\
    abi_allocation_trace 32 ids ss (abi_native_complex_entry head_size cs ss)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cs.cs_next_id`, `cs.cs_next_var`, `32`, `ids`, `ss`]
    mp_tac buffer_allocation_budget_window >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`head_size`, `cs`, `ss`] strip_assume_tac abi_native_complex_entry_context >>
  conj_tac
  >- fs[abi_allocator_state_eq, abi_allocated_window_def, abi_static_loop_counter_snapshot] >>
  simp_tac bool_ss [abi_allocation_trace_def] >> qexists_tac `[cs.cs_next_id]` >>
  simp[abi_allocation_sequence_cons, abi_allocator_state_def, abi_native_complex_entry_def,
    abi_complex_prefix_state_def, abi_static_loop_alloc_frame_snapshot, update_var_def,
    mstore_def, write_memory_with_expansion_def, memory_snapshot_allocated_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed exact complex entry state and resources: " ^ name)
  end) (DB.thms "abiNativeComplexPrefixState")
