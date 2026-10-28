(* TOP-LEVEL: actual setup preserves the complete source and destination
   length header, initializes the two counters and establishes the empty
   packed-prefix array invariant. *)
Theory abiNativeDynamicArrayStartData
Ancestors
  abiNativeDynamicArrayStartValues abiNativeDynamicArrayStartState abiNativeDynamicArrayStartCode abiNativeDynamicArrayState
  abiNativeDynamicArraySource abiNativeArraySource abiNativeTraversalRead abiNativeTraversal abiNativeEncodingDefs abiNativeCursor
  abiAllocatedWindows abiMemoryEncoding abiMemoryFrame abiFieldMemory abiFieldLayoutDefs memoryReadProps
  abiStaticLoopEntry compileAllocaProvenance compileEnv venomMemDefs venomState venomInst list words arithmetic

Theorem abi_native_dynamic_array_start_data:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride ss dst src len_op.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) ss /\
    abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) ss cs
      (abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss) /\
    abi_native_cursor func cs after (abi_native_dynamic_array_index_inst cs)
      (abi_static_loop_counter_addr cs.cs_next_id ss) (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
      (abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss) /\
    abi_native_cursor func cs after (abi_native_dynamic_array_tail_inst cs)
      (abi_native_dynamic_array_tail_addr cs ss) (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
      (abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss) /\
    abi_allocated_window ss target_id (w2n dst_addr) 32 /\ w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ 32 <= source_capacity /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) (source_capacity - 32) ss.vs_memory fields /\
    mload (w2n root_addr) ss = n2w (LENGTH fields) /\ mload (w2n dst_addr) ss = n2w (LENGTH fields) ==>
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr (abi_static_loop_counter_addr cs.cs_next_id ss)
      (abi_native_dynamic_array_tail_addr cs ss) source_capacity 0 (abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss)
Proof
  rpt gen_tac >> strip_tac >>
  `alloca_inv ss /\ ~MEM target_id (compiler_alloca_ids cs after)` by fs[abi_native_memory_ready_def] >>
  drule_all abi_native_traversal_allocation >> strip_tac >>
  `abi_allocated_window (abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss) cs.cs_next_id
    (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) 32 /\
    abi_allocated_window (abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss) (cs.cs_next_id + 2)
    (w2n (abi_native_dynamic_array_tail_addr cs ss)) 32` by
    fs[abi_native_cursor_def, abi_native_dynamic_array_index_inst_def, abi_native_dynamic_array_tail_inst_def, mk_inst_def] >>
  drule_all abi_native_dynamic_array_start_values >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr + 32w`,
    `abi_field_bytes (abi_field_head_size fields) fields`, `ss`, `cs`, `abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss`,
    `REPLICATE (LENGTH fields) (info,width,stride,T)`, `fields`, `n2w (LENGTH fields)`]
    mp_tac abi_native_array_source >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `mload (w2n dst_addr) (abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss) = mload (w2n dst_addr) ss` by
    (qspecl_then [`ctx`, `func`, `cs`, `after`, `dst_addr + 32w`, `abi_field_bytes (abi_field_head_size fields) fields`, `ss`, `cs`,
       `abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss`, `target_id`, `w2n dst_addr`, `32`]
       mp_tac abi_native_traversal_owned_read >>
     impl_tac >- asm_simp_tac (srw_ss()) [abi_window_separated_def, compileEnvTheory.regions_disjoint_def] >>
     disch_then (mp_tac o AP_TERM ``word_of_bytes T (0w:bytes32)``) >> simp_tac bool_ss [GSYM mload_read_memory]) >>
  drule_all abi_native_dynamic_array_shape >> strip_tac >>
  irule abi_native_dynamic_array_initial >> asm_simp_tac (srw_ss()) [word_mul_n2w]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed initial full dynamic array data after actual setup: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayStartData")
