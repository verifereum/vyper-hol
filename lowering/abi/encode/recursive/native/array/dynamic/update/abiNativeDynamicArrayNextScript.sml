(* TOP-LEVEL: assemble the real post-child execution into the next full
   traversal, ready state, source/output invariant and two loop cursors. *)
Theory abiNativeDynamicArrayNext
Ancestors
  abiNativeDynamicArrayUpdateTraversal abiNativeDynamicArrayUpdateFrame abiNativeDynamicArrayNextLayout
  abiNativeDynamicArrayNextReady abiNativeDynamicArrayNextData abiNativeDynamicArrayUpdateState
  abiNativeDynamicArrayBounds abiNativeDynamicArrayState abiNativeDynamicArrayParts
  abiNativeTraversal abiNativeEncodingDefs abiNativeCursor abiNativeCursorLoop abiDynamicLoopRun abiDynamicLoopIteration
  abiDynamicLoopCode abiDynamicLoopStep abiFieldMemory abiFieldLayoutDefs abiFieldOperands abiStaticLoopCode
  abiMemoryLeafRun abiAllocatedWindows compileAllocaProvenance compileEnv fragExec venomMemDefs venomState venomInst list words arithmetic

Theorem abi_native_dynamic_array_next:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride initial
      dst src len_op ret mid child_len ss index counter_addr dyn_addr out dyn_inst index_inst.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) initial mid out /\
    abi_dynamic_loop_ready cs dst src len_op dst_addr root_addr counter_addr dyn_addr (LENGTH fields) index ss /\
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity index ss /\
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity 0 initial /\
    abi_allocated_window initial target_id (w2n dst_addr) 32 /\
    abi_native_encoding_result ctx func (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid child_len
      (dst_addr + 32w + mload (w2n dyn_addr) ss) (SND (EL index fields))
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr (n2w (LENGTH fields)) ss) out /\
    abi_dynamic_loop_child_return cs.cs_next_var mid child_len dst_addr width counter_addr dyn_addr
      (n2w index) (mload (w2n dyn_addr) ss) (n2w (LENGTH (SND (EL index fields)))) out /\ ~out.vs_halted /\
    abi_fields_layout (TAKE index fields) (w2n dst_addr + 32) 0 (abi_field_head_size fields) out /\
    read_memory (w2n dst_addr + 32 + abi_field_head_size fields + abi_field_tail_size (TAKE index fields))
      (LENGTH (SND (EL index fields))) out = SND (EL index fields) /\
    abi_native_cursor func cs after dyn_inst dyn_addr mid out /\ abi_native_cursor func cs after index_inst counter_addr mid out /\
    compiler_instruction_member (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) dyn_inst /\
    compiler_instruction_member (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) index_inst /\
    dyn_inst.inst_id <> index_inst.inst_id /\ w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ index < LENGTH fields /\
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\ fn_has_code cs after func /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\
    abi_operand_before (cs.cs_next_var + 3) dst /\ abi_operand_before (cs.cs_next_var + 3) src /\
    abi_operand_before (cs.cs_next_var + 3) len_op ==>
    let next = abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index
      (mload (w2n dyn_addr) ss) (n2w (LENGTH (SND (EL index fields)))) out in
    abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) initial cs next /\
    abi_dynamic_loop_ready cs dst src len_op dst_addr root_addr counter_addr dyn_addr (LENGTH fields) (index + 1) next /\
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity (index + 1) next /\
    abi_native_cursor func cs after dyn_inst dyn_addr (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) next /\
    abi_native_cursor func cs after index_inst counter_addr (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) next
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `cs.cs_next_var + 15 <= mid.cs_next_var` by (drule_all abi_native_dynamic_array_parts >> simp[]) >>
  qpat_assum `abi_native_dynamic_array_data _ _ _ _ _ _ _ _ _ index ss`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_dynamic_array_data_def]) >>
  drule_all abi_native_dynamic_array_element_bounds >> strip_tac >>
  `w2n (dst_addr + 32w) <= w2n (dst_addr + 32w + n2w index * n2w width) /\
    w2n (dst_addr + 32w + n2w index * n2w width) + 32 <=
      w2n (dst_addr + 32w) + LENGTH (abi_field_bytes (abi_field_head_size fields) fields)` by
    (qpat_assum `w2n (dst_addr + 32w + n2w index * n2w width) = _`
       (fn th => PURE_REWRITE_TAC [th, abi_field_bytes_length]) >> decide_tac) >>
  drule_all abi_native_dynamic_array_next_traversal >> DISCH_TAC >>
  qspecl_then [`func`, `cs`, `after`, `cs`, `mid`, `dst_addr`, `width`, `counter_addr`, `dyn_addr`, `index`,
    `mload (w2n dyn_addr) ss`, `n2w (LENGTH (SND (EL index fields)))`, `out`, `dyn_inst`, `index_inst`,
    `dst_addr + 32w`, `abi_field_bytes (abi_field_head_size fields) fields`]
    mp_tac abi_native_dynamic_array_next_cursor_frame >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_native_dynamic_array_next_layout >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cs`, `dst`, `src`, `width`, `stride`, `len_op`, `mid`, `child_len`, `dst_addr`, `root_addr`,
    `counter_addr`, `dyn_addr`, `n2w (LENGTH fields)`, `ss`, `out`, `dst_addr + 32w + mload (w2n dyn_addr) ss`,
    `SND (EL index fields)`, `index`, `mload (w2n dyn_addr) ss`, `n2w (LENGTH (SND (EL index fields)))`]
    mp_tac abi_native_dynamic_array_next_operands >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  drule_all abi_native_dynamic_array_next_ready >> DISCH_TAC >>
  `index + 1 <= LENGTH fields` by decide_tac >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`, `fields`,
    `info`, `width`, `stride`, `initial`, `cs`,
    `abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index (mload (w2n dyn_addr) ss)
      (n2w (LENGTH (SND (EL index fields)))) out`, `index + 1`, `counter_addr`, `dyn_addr`]
    mp_tac abi_native_dynamic_array_data_traversal >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    (irule abi_native_cursor_context >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     qexists_tac `mid` >> first_assum MATCH_ACCEPT_TAC)]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual next complete dynamic array loop invariant: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayNext")
