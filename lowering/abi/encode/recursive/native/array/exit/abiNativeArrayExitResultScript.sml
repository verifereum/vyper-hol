(* TOP-LEVEL: the real parent epilogue returns the complete encoding while
   preserving its packed bytes. Its scratch frame uses the actual enclosing
   allocation profile, and it performs no new allocation. *)
Theory abiNativeArrayExitResult
Ancestors
  abiNativeArrayExitState abiNativeComplexPrefixReady abiNativeCursor abiNativeEncodingDefs abiMemoryLeafRun
  abiDynArrayCode abiAllocatedMemoryFrame abiAllocatedWindows abiAllocationWindows abiAllocatorState
  abiMemoryFrame abiFieldOperands compileAllocaProvenance compileEnv fragExec venomMemDefs venomState list words arithmetic

Theorem abi_native_array_exit_result:
  !ctx func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload parent_inst parent_addr
      parent_ptr encoded_size cs ss.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity (dst_addr:bytes32) payload ss /\
    abi_native_cursor func root_cs root_after parent_inst parent_addr cs ss /\
    fn_has_code cs (abi_dynarray_exit_cut parent_ptr encoded_size cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand parent_ptr ss = SOME parent_addr /\ eval_operand encoded_size ss = SOME (n2w (LENGTH payload)) /\
    mload (w2n parent_addr) ss = 0w /\ read_memory (w2n dst_addr) (LENGTH payload) ss = payload /\
    abi_operand_before cs.cs_next_var parent_ptr /\ abi_operand_before cs.cs_next_var encoded_size ==>
    abi_encoding_result ctx func cs (abi_dynarray_exit_cut parent_ptr encoded_size cs)
      (Var (compiler_var_name cs.cs_next_var 2)) dst_addr payload
      (abi_allocation_windows (compiler_alloca_ids root_cs root_after)
        (abi_native_array_exit_boundary cs parent_addr (n2w (LENGTH payload)) ss))
      ss (abi_native_array_exit_boundary cs parent_addr (n2w (LENGTH payload)) ss) /\
    abi_allocator_state (abi_native_array_exit_boundary cs parent_addr (n2w (LENGTH payload)) ss) = abi_allocator_state ss
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
  drule_all abi_native_cursor_root_distinct >> strip_tac >>
  qpat_assum `abi_native_cursor _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  qspecl_then [`ctx`, `func`, `parent_ptr`, `encoded_size`, `cs`, `ss`, `parent_addr`, `n2w (LENGTH payload)`]
    mp_tac abi_native_array_exit_path >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`cs`, `parent_ptr`, `encoded_size`, `parent_addr`, `n2w (LENGTH payload)`, `ss`]
    mp_tac abi_native_array_exit_context >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`ss`, `ss`, `abi_native_array_exit_boundary cs parent_addr (n2w (LENGTH payload)) ss`,
    `[(parent_inst.inst_id,(w2n parent_addr,32))]`, `target_id`, `w2n dst_addr`, `LENGTH payload`]
    mp_tac abi_allocated_memory_frame_read >> impl_tac >- fs[alloca_inv_def] >> DISCH_TAC >>
  `abi_native_cursor func root_cs root_after parent_inst parent_addr cs
    (abi_native_array_exit_boundary cs parent_addr (n2w (LENGTH payload)) ss)` by
    fs[abi_native_cursor_def, abi_allocated_window_def, abi_allocator_state_eq] >>
  qspecl_then [`func`, `root_cs`, `root_after`, `parent_inst`, `parent_addr`, `cs`, `ss`,
    `abi_native_array_exit_boundary cs parent_addr (n2w (LENGTH payload)) ss`, `dst_addr`, `payload`]
    mp_tac abi_native_cursor_store_frame >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==>
    eval_operand arg_op (abi_native_array_exit_boundary cs parent_addr (n2w (LENGTH payload)) ss) = eval_operand arg_op ss` by
    (rpt strip_tac >> drule_all abi_native_array_exit_old_operand >> simp[]) >>
  conj_tac >- (PURE_REWRITE_TAC [abi_encoding_result_def] >> asm_simp_tac (srw_ss()) []) >>
  first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native array epilogue result: " ^ name)
  end) (DB.thms "abiNativeArrayExitResult")
