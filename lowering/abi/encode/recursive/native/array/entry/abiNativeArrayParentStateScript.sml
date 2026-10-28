(* TOP-LEVEL: actual array parent setup has one uniform allocation trace,
   whether its cell is fresh or cached. It frames external state and old
   operands while writing only the parent cell and output length header. *)
Theory abiNativeArrayParentState
Ancestors
  abiDynArrayCode abiDynArrayEnds abiDynArrayBoundaryFrames abiDynBytesAllocState abiStaticLoopEntry abiStaticLoopCode
  abiBufferBudgetPath abiAllocationTrace abiAllocationSequence abiAllocatedWindows abiAllocatorState
  abiStateFrame abiStateLoopFrame abiMemoryFrame abiFieldOperands memoryValueSnapshot
  compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_array_parent_context:
  !cs dst_addr root_addr ss.
    abi_allocator_state (abi_dynarray_entry_boundary cs dst_addr root_addr ss) =
      abi_allocator_state (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var 32 ss) /\
    abi_state_frame ss (abi_dynarray_entry_boundary cs dst_addr root_addr ss) /\
    abi_memory_frame [(w2n (abi_static_loop_counter_addr cs.cs_next_id ss),32);(w2n dst_addr,32)] ss
      (abi_dynarray_entry_boundary cs dst_addr root_addr ss)
Proof
  rpt gen_tac >> qspecl_then [`cs`, `dst_addr`, `root_addr`, `ss`]
    strip_assume_tac abi_dyn_bytes_boundary_allocation_fields >>
  simp[abi_allocator_state_eq, memory_snapshot_allocated_def, update_var_def, abi_state_frame_def,
    abi_dynarray_entry_boundary_frame]
QED

Theorem abi_native_array_parent_old_operand:
  !cs dst_addr root_addr ss arg_op.
    abi_operand_before cs.cs_next_var arg_op ==>
    eval_operand arg_op (abi_dynarray_entry_boundary cs dst_addr root_addr ss) = eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> irule abi_dynarray_entry_boundary_operand >>
  qpat_x_assum `abi_operand_before _ _` (mp_tac o PURE_REWRITE_RULE [abi_operand_before_def]) >> DISCH_TAC >>
  conj_tac
  >- (first_x_assum (qspec_then `cs.cs_next_var` mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `cs.cs_next_var + 1` mp_tac) >> simp[compiler_var_name_add, compiler_var_name_def]
QED

Theorem abi_native_array_parent_path:
  !ctx func cs dst src dst_addr root_addr ss.
    fn_has_code cs (abi_dynarray_entry_cut dst src cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr ==>
    fragment_path ctx func ss (abi_dynarray_entry_boundary cs dst_addr root_addr ss)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`ctx`, `func`, `dst`, `src`, `cs`, `ss`, `dst_addr`, `root_addr`]
    mp_tac abi_dynarray_entry_boundary_path >>
  impl_tac >- (asm_simp_tac bool_ss [] >> fs[abi_operand_before_def, compiler_var_name_def] >>
    rpt conj_tac >> first_assum irule >> decide_tac) >> simp_tac bool_ss []
QED

Theorem abi_native_array_parent_allocation:
  !cs dst_addr root_addr ids ss.
    MEM cs.cs_next_id ids /\ abi_alloca_budget 32 ids ss < dimword (:256) /\
    abi_alloca_request_ok cs.cs_next_id 32 ss /\ alloca_inv ss ==>
    abi_allocated_window (abi_dynarray_entry_boundary cs dst_addr root_addr ss) cs.cs_next_id
      (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) 32 /\
    abi_allocation_trace 32 ids ss (abi_dynarray_entry_boundary cs dst_addr root_addr ss)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cs.cs_next_id`, `cs.cs_next_var`, `32`, `ids`, `ss`]
    mp_tac buffer_allocation_budget_window >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`cs`, `dst_addr`, `root_addr`, `ss`] strip_assume_tac abi_native_array_parent_context >>
  conj_tac
  >- fs[abi_allocator_state_eq, abi_allocated_window_def, abi_static_loop_counter_snapshot] >>
  simp_tac bool_ss [abi_allocation_trace_def] >> qexists_tac `[cs.cs_next_id]` >>
  simp[abi_allocation_sequence_cons, abi_allocator_state_def, abi_dynarray_entry_boundary_def,
    abi_dynarray_entry_state_def, abi_static_loop_entry_state_def, abi_static_loop_alloc_frame_snapshot,
    memory_snapshot_allocated_def, update_var_def, mstore_def, write_memory_with_expansion_def, LET_THM]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native array parent setup state: " ^ name)
  end) (DB.thms "abiNativeArrayParentState")
