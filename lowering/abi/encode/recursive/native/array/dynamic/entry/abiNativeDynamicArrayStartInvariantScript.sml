(* TOP-LEVEL: actual setup establishes every resource of the runtime loop
   at its initial header. The original source observation is retained for
   semantic recursive children, and the owned length header survives. *)
Theory abiNativeDynamicArrayStartInvariant
Ancestors
  abiNativeDynamicArrayStartTraversal abiNativeDynamicArrayStartData abiNativeDynamicArrayStartValues
  abiNativeDynamicArrayStartCode abiNativeDynamicArrayStartState abiNativeDynamicArrayInvariant abiNativeDynamicArrayState
  abiNativeTraversal abiNativeArrayBudget abiNativeEncodingDefs abiNativeCursor abiWriterFrame abiAllocatedWindows
  abiDynamicLoopCode abiStaticLoopEntry abiFieldOperands abiFieldLayoutDefs compileAllocaProvenance compileEnv fragExec
  venomMemDefs venomState venomInst list words arithmetic

Theorem abi_native_dynamic_array_start_invariant:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride ss dst src len_op ret child_len mid.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) ss /\
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\ fn_has_code cs after func /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\ eval_operand len_op ss = SOME (n2w (LENGTH fields)) /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\ abi_operand_before cs.cs_next_var len_op /\
    abi_allocated_window ss target_id (w2n dst_addr) 32 /\ w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ 32 <= source_capacity /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) (source_capacity - 32) ss.vs_memory fields /\
    mload (w2n root_addr) ss = n2w (LENGTH fields) /\ mload (w2n dst_addr) ss = n2w (LENGTH fields) ==>
    let header = abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss in
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) header /\
    abi_native_dynamic_array_invariant ctx func cs after dst src len_op dst_addr root_addr
      (abi_static_loop_counter_addr cs.cs_next_id ss) (abi_native_dynamic_array_tail_addr cs ss)
      info width stride fields source_capacity header (abi_native_dynamic_array_tail_inst cs) (abi_native_dynamic_array_index_inst cs) 0 header /\
    abi_allocated_window header target_id (w2n dst_addr) 32 /\
    mem_bytes_at (w2n root_addr) source_capacity header.vs_memory = mem_bytes_at (w2n root_addr) source_capacity ss.vs_memory
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `alloca_inv ss /\ compiler_id_history cs` by fs[abi_native_memory_ready_def] >>
  `cs_extends after after` by simp[cs_extends_refl] >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `dst_addr + 32w`, `abi_field_bytes (abi_field_head_size fields) fields`, `ss`]
    mp_tac abi_native_traversal_initial >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  drule_all abi_native_dynamic_array_start_traversal >> strip_tac >>
  drule_all abi_native_dynamic_array_start_data >> DISCH_TAC >>
  drule_all abi_native_traversal_allocation >> strip_tac >>
  `abi_allocated_window (abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss) cs.cs_next_id
    (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) 32 /\
    abi_allocated_window (abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss) (cs.cs_next_id + 2)
    (w2n (abi_native_dynamic_array_tail_addr cs ss)) 32` by
    fs[abi_native_cursor_def, abi_native_dynamic_array_index_inst_def, abi_native_dynamic_array_tail_inst_def, mk_inst_def] >>
  qspecl_then [`cs`, `dst`, `src`, `len_op`, `dst_addr`, `root_addr`, `width`, `LENGTH fields`, `ss`]
    mp_tac abi_native_dynamic_array_start_ready >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `abi_allocated_window (abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss) target_id (w2n dst_addr) 32` by
    (qspecl_then [`ss`, `abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss`, `target_id`, `w2n dst_addr`, `32`]
       mp_tac allocation_growth_window >> impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []) >>
  drule_all abi_native_traversal_source >> DISCH_TAC >>
  drule_all abi_native_traversal_root_ready >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `dst_addr + 32w`, `abi_field_bytes (abi_field_head_size fields) fields`,
    `abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss`] mp_tac abi_native_traversal_initial >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  asm_simp_tac bool_ss [abi_native_dynamic_array_invariant_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete actual dynamic array initial header invariant: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayStartInvariant")
