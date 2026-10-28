(* TOP-LEVEL: the child bytes and retained packed prefix become the next
   array layout after the real stores, latch and header jump. *)
Theory abiNativeDynamicArrayNextLayout
Ancestors
  abiNativeDynamicArrayUpdateLayout abiNativeDynamicArrayUpdateState abiNativeDynamicArraySource abiNativeDynamicArrayBounds
  abiNativeDynamicArrayState abiNativeTraversalReady abiNativeTraversal abiNativeCursor abiNativeEncodingDefs
  abiAllocatedWindows abiFieldMemory abiFieldLayoutDefs abiStaticLoopBody abiDynamicLoopUpdate abiDynamicLoopCode
  compileAllocaProvenance compileEnv fragExec venomMemDefs venomState venomInst list words arithmetic

Theorem abi_native_dynamic_array_layout_jump:
  !fields arena head_offset tail_offset label ss.
    abi_fields_layout fields arena head_offset tail_offset (jump_to label ss) <=>
    abi_fields_layout fields arena head_offset tail_offset ss
Proof
  simp[abi_fields_layout_def, memory_reads_jump_to]
QED

Theorem abi_native_dynamic_array_next_layout:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride initial
      mid ss index counter_addr dyn_addr out dyn_inst index_inst.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) initial mid out /\
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity index ss /\
    abi_native_cursor func cs after dyn_inst dyn_addr mid out /\ abi_native_cursor func cs after index_inst counter_addr mid out /\
    dyn_inst.inst_id <> index_inst.inst_id /\ w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ index < LENGTH fields /\
    abi_fields_layout (TAKE index fields) (w2n dst_addr + 32) 0 (abi_field_head_size fields) out /\
    read_memory (w2n dst_addr + 32 + abi_field_head_size fields + abi_field_tail_size (TAKE index fields))
      (LENGTH (SND (EL index fields))) out = SND (EL index fields) ==>
    let next = abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index
      (mload (w2n dyn_addr) ss) (n2w (LENGTH (SND (EL index fields)))) out in
    abi_fields_layout (TAKE (index + 1) fields) (w2n dst_addr + 32) 0 (abi_field_head_size fields) next /\
    mload (w2n counter_addr) next = n2w (index + 1) /\
    mload (w2n dyn_addr) next = n2w (abi_field_head_size fields + abi_field_tail_size (TAKE (index + 1) fields))
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `alloca_inv initial /\ ~MEM source_id (compiler_alloca_ids cs after) /\ ~MEM target_id (compiler_alloca_ids cs after)` by
    fs[abi_native_memory_ready_def] >>
  drule_all abi_native_traversal_allocation >> strip_tac >> drule_all abi_native_traversal_windows >> strip_tac >>
  qspecl_then [`func`, `cs`, `after`, `dyn_inst`, `dyn_addr`, `mid`, `out`, `source_id`, `target_id`]
    mp_tac abi_native_cursor_root_distinct >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`func`, `cs`, `after`, `index_inst`, `counter_addr`, `mid`, `out`, `source_id`, `target_id`]
    mp_tac abi_native_cursor_root_distinct >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_native_dynamic_array_data _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_dynamic_array_data_def]) >>
  drule_all abi_native_dynamic_array_element_bounds >> strip_tac >>
  drule_all abi_native_dynamic_array_take_step >> strip_tac >> drule_all abi_native_dynamic_array_ranges >> strip_tac >>
  `abi_allocated_window out target_id (w2n dst_addr + 32) (LENGTH (abi_field_bytes (abi_field_head_size fields) fields))` by
    (qpat_assum `w2n (dst_addr + 32w) = _` (fn th =>
       qpat_assum `abi_allocated_window out target_id _ (LENGTH (abi_field_bytes _ fields))`
         (MATCH_ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  `abi_allocated_window out dyn_inst.inst_id (w2n dyn_addr) 32 /\
    abi_allocated_window out index_inst.inst_id (w2n counter_addr) 32` by fs[abi_native_cursor_def] >>
  qspecl_then [`mid`, `dst_addr + 32w + n2w index * n2w width`, `dyn_addr`, `counter_addr`, `n2w index`, `out`,
    `target_id`, `dyn_inst.inst_id`, `index_inst.inst_id`, `w2n dst_addr + 32`,
    `LENGTH (abi_field_bytes (abi_field_head_size fields) fields)`, `TAKE index fields`, `abi_field_head_size fields`,
    `SND (EL index fields)`] mp_tac abi_native_dynamic_array_update_layout >>
  impl_tac >- (asm_simp_tac bool_ss [abi_field_bytes_length, EQ_SYM_EQ] >> decide_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_assum `width = 32` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac (srw_ss()) [abi_native_dynamic_array_next_state_def, abi_native_dynamic_array_layout_jump,
    memory_reads_jump_to, GSYM ADD1, word_add_n2w, abi_field_tail_size_append,
    abi_field_tail_def, ADD_ASSOC]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual next packed array prefix and counter values: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayNextLayout")
