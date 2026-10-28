(* TOP-LEVEL: the two real setup requests establish both owned counter
   cells under the computed allocation budget, including cached replay. *)
Theory abiNativeDynamicArrayStartWindows
Ancestors
  abiNativeDynamicArrayStartState abiDynamicLoopEntry abiStaticLoopEntry abiDynBytesAllocState
  abiAllocationTrace abiAllocationBudgetNested abiAllocationBudget abiAllocationSequence abiBufferBudgetPath
  abiAllocatedWindows abiAllocatorState memoryValueSnapshot compileEnv fragExec venomMemDefs venomState list words arithmetic
Libs wordsLib

Theorem abi_native_dynamic_array_start_first_trace:
  !cs ids ss.
    MEM cs.cs_next_id ids ==>
    abi_allocation_trace 32 ids ss (abi_static_loop_entry_state cs.cs_next_id cs.cs_next_var ss)
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [abi_allocation_trace_def] >> qexists_tac `[cs.cs_next_id]` >>
  simp[abi_allocator_state_def, abi_static_loop_entry_allocation_fields]
QED

Theorem abi_native_dynamic_array_start_tail_allocator:
  !cs width length_word ss.
    abi_allocator_state (abi_native_dynamic_array_start_state cs width length_word ss) =
      abi_allocator_state (memory_snapshot_allocated (cs.cs_next_id + 2) (cs.cs_next_var + 1) 32
        (abi_static_loop_entry_state cs.cs_next_id cs.cs_next_var ss))
Proof
  simp[abi_native_dynamic_array_start_state_def, abi_dynamic_loop_entry_state_def, abi_dynamic_loop_entry_tail_state_def,
    memory_snapshot_allocated_def, abi_static_loop_alloc_frame_snapshot, LET_THM]
QED

Theorem abi_native_dynamic_array_start_tail_trace:
  !cs width length_word ids ss.
    MEM (cs.cs_next_id + 2) ids ==>
    abi_allocation_trace 32 ids (abi_static_loop_entry_state cs.cs_next_id cs.cs_next_var ss)
      (abi_native_dynamic_array_start_state cs width length_word ss)
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [abi_allocation_trace_def] >> qexists_tac `[cs.cs_next_id + 2]` >>
  simp[abi_native_dynamic_array_start_tail_allocator, abi_allocator_state_def, memory_snapshot_allocated_def, update_var_def]
QED

Theorem abi_native_dynamic_array_start_windows:
  !cs width length_word ids ss.
    MEM cs.cs_next_id ids /\ MEM (cs.cs_next_id + 2) ids /\
    abi_alloca_budget 32 ids ss < dimword (:256) /\ alloca_inv ss /\
    abi_alloca_request_ok cs.cs_next_id 32 ss /\ abi_alloca_request_ok (cs.cs_next_id + 2) 32 ss ==>
    abi_allocated_window (abi_native_dynamic_array_start_state cs width length_word ss) cs.cs_next_id
      (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) 32 /\
    abi_allocated_window (abi_native_dynamic_array_start_state cs width length_word ss) (cs.cs_next_id + 2)
      (w2n (abi_native_dynamic_array_tail_addr cs ss)) 32
Proof
  rpt gen_tac >> strip_tac >>
  `32 < dimword (:256)` by simp_tac (srw_ss() ++ SIZES_ss) [] >>
  qspecl_then [`cs`, `ids`, `ss`] mp_tac abi_native_dynamic_array_start_first_trace >> impl_tac >- simp[] >> DISCH_TAC >>
  `alloca_inv (abi_static_loop_entry_state cs.cs_next_id cs.cs_next_var ss)` by
    (drule_all abi_allocation_trace_inv >> simp[]) >>
  drule_all abi_allocation_trace_budget >> DISCH_TAC >>
  qspecl_then [`32`, `ids`, `ss`, `abi_static_loop_entry_state cs.cs_next_id cs.cs_next_var ss`, `cs.cs_next_id + 2`]
    mp_tac abi_allocation_trace_request >> impl_tac >- simp[] >> DISCH_TAC >>
  `abi_allocated_window (abi_static_loop_entry_state cs.cs_next_id cs.cs_next_var ss) cs.cs_next_id
    (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) 32` by
    (qspecl_then [`cs.cs_next_id`, `cs.cs_next_var`, `32`, `ids`, `ss`] mp_tac buffer_allocation_budget_window >>
     impl_tac >- asm_simp_tac bool_ss [] >> simp[abi_allocated_window_def, abi_static_loop_entry_allocation_fields,
       memory_snapshot_allocated_def, update_var_def, abi_static_loop_counter_snapshot]) >>
  conj_tac >- (
    qspecl_then [`cs`, `width`, `length_word`, `ids`, `ss`] mp_tac abi_native_dynamic_array_start_tail_trace >>
    impl_tac >- simp[] >> DISCH_TAC >>
    qspecl_then [`32`, `ids`, `abi_static_loop_entry_state cs.cs_next_id cs.cs_next_var ss`,
      `abi_native_dynamic_array_start_state cs width length_word ss`, `cs.cs_next_id`,
      `w2n (abi_static_loop_counter_addr cs.cs_next_id ss)`, `32`] mp_tac abi_allocation_trace_window >> simp[]) >>
  qspecl_then [`cs.cs_next_id + 2`, `cs.cs_next_var + 1`, `32`, `ids`, `abi_static_loop_entry_state cs.cs_next_id cs.cs_next_var ss`]
    mp_tac buffer_allocation_budget_window >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`cs`, `width`, `length_word`, `ss`] mp_tac abi_native_dynamic_array_start_tail_allocator >>
  simp_tac bool_ss [abi_allocator_state_eq] >> strip_tac >>
  fs[abi_allocated_window_def, abi_native_dynamic_array_tail_addr_def, abi_static_loop_counter_snapshot]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array setup counter allocation windows: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayStartWindows")
