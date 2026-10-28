(* TOP-LEVEL: actual static index setup allocates or reuses one counter,
   zeros it and jumps to the generated header. Its trace is a single
   computed-profile request, and old SSA operands remain unchanged. *)
Theory abiNativeStaticStartState
Ancestors
  abiNativeStaticHeaderCode abiStaticLoopEntry abiStaticLoopCode abiStaticLoopCodeProps abiStaticLoopBody
  abiDynBytesAllocState abiDynamicLoopEntryFrames abiStateLoopFrame abiStateFrame abiStateFrameOps abiAllocatorState
  abiBufferBudgetPath abiAllocationTrace abiAllocationSequence abiAllocatedWindows abiMemoryFrame abiFieldOperands
  memoryValueSnapshot compileEnv fragExec venomMemDefs venomState list rich_list words arithmetic

Theorem abi_native_static_start_context:
  !cs ss.
    (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss).vs_current_bb =
      (abi_native_static_header_cut cs).cs_current_bb /\
    (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss).vs_inst_idx =
      LENGTH (abi_native_static_header_cut cs).cs_current_insts /\
    (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss).vs_halted = ss.vs_halted /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0))
      (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) =
      SOME (abi_static_loop_counter_addr cs.cs_next_id ss) /\
    mload (w2n (abi_static_loop_counter_addr cs.cs_next_id ss))
      (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) = 0w /\
    abi_state_frame ss (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) /\
    abi_allocator_state (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) =
      abi_allocator_state (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var 32 ss) /\
    abi_memory_frame [(w2n (abi_static_loop_counter_addr cs.cs_next_id ss),32)] ss
      (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss)
Proof
  rpt gen_tac >>
  `abi_memory_frame [(w2n (abi_static_loop_counter_addr cs.cs_next_id ss),32)] ss
    (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss)` by
    (qspecl_then [`cs.cs_next_id`, `cs.cs_next_var`, `ss`] mp_tac abi_static_loop_entry_memory_frame >>
     simp[abi_memory_frame_def, abi_static_loop_start_state_def, read_memory_def, jump_to_def]) >>
  simp_tac (srw_ss()) [abi_native_static_header_cut_def, abi_static_loop_start_counter] >>
  simp[abi_static_loop_start_state_def, abi_state_frame_def, abi_static_loop_entry_state_def,
    abi_static_loop_alloc_frame_snapshot, memory_snapshot_allocated_def] >>
  simp[GSYM abi_static_loop_alloc_frame_snapshot, abi_state_context_alloca]
QED

Theorem abi_native_static_start_old_operand:
  !cs ss arg_op.
    abi_operand_before cs.cs_next_var arg_op ==>
    eval_operand arg_op (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) = eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> irule abi_static_loop_start_operand_frame >>
  qpat_x_assum `abi_operand_before _ _` (mp_tac o PURE_REWRITE_RULE [abi_operand_before_def]) >>
  disch_then (qspec_then `cs.cs_next_var` mp_tac) >> simp[]
QED

Theorem abi_native_static_start_trace:
  !cs ids ss.
    MEM cs.cs_next_id ids ==>
    abi_allocation_trace 32 ids ss (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss)
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [abi_allocation_trace_def] >> qexists_tac `[cs.cs_next_id]` >>
  simp[abi_allocation_sequence_cons, abi_native_static_start_context, abi_allocator_state_def,
    memory_snapshot_allocated_def, update_var_def]
QED

Theorem abi_native_static_start_window:
  !cs ids ss.
    MEM cs.cs_next_id ids /\ abi_alloca_budget 32 ids ss < dimword (:256) /\
    abi_alloca_request_ok cs.cs_next_id 32 ss /\ alloca_inv ss ==>
    abi_allocated_window (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) cs.cs_next_id
      (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) 32
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cs.cs_next_id`, `cs.cs_next_var`, `32`, `ids`, `ss`]
    mp_tac buffer_allocation_budget_window >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`cs`, `ss`] strip_assume_tac abi_native_static_start_context >>
  fs[abi_allocator_state_eq, abi_allocated_window_def, abi_static_loop_counter_snapshot]
QED

Theorem abi_native_static_start_path:
  !ctx func dst src info width stride len_op cs ret after ss.
    compile_abi_encode_dyn_static_loop dst src info width stride len_op cs = (ret,after) /\ fn_has_code cs after func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    fragment_path ctx func ss (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_abi_encode_dyn_static_loop_contains >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block cs.cs_current_bb _ = SOME entry_bb` >>
  qmatch_asmsub_abbrev_tac `lookup_block (fresh_label_output "enc_dyn_hdr" cs.cs_next_label) _ = SOME header_bb` >>
  qspecl_then [`ctx`, `func`, `cs.cs_next_id`, `cs.cs_next_var`, `cs.cs_next_label`, `ss`, `entry_bb`, `header_bb`]
    mp_tac abi_static_loop_entry_path >>
  impl_tac >- asm_simp_tac (srw_ss()) [Abbr`entry_bb`, Abbr`header_bb`, abi_static_loop_blocks_no_phi, DROP_LENGTH_APPEND] >>
  simp_tac bool_ss [abi_static_loop_start_state_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual static index setup state and execution: " ^ name)
  end) (DB.thms "abiNativeStaticStartState")
