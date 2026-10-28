(* TOP-LEVEL: actual recursive execution preserves each separately owned
   loop counter. The counter's real allocation instruction is older than
   the child, so its allocation identity is excluded from child scratch. *)
Theory abiNativeDynamicArrayCallCursor
Ancestors
  abiNativeDynamicArrayPrefixState abiNativeCursor abiNativeCursorFrame abiNativeResources abiNativeEncodingDefs
  abiAllocatedWindows abiAllocatorState abiDynamicLoopStep abiDynamicLoopCode abiStaticLoopCode
  compileEnv fragExec venomMemDefs venomState list words arithmetic

Theorem abi_native_cursor_allocator_state:
  !func root_cs root_after counter_inst read_addr cs before after.
    abi_allocator_state after = abi_allocator_state before ==>
    (abi_native_cursor func root_cs root_after counter_inst read_addr cs after <=>
     abi_native_cursor func root_cs root_after counter_inst read_addr cs before)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocator_state_eq] >> strip_tac >>
  simp[abi_native_cursor_def, abi_allocated_window_def]
QED

Theorem abi_native_dynamic_array_call_cursor:
  !ctx func cs after counter_inst read_addr dst src width stride len_op dst_addr root_addr counter_addr dyn_addr length_word ss
      source_id target_id source_addr span payload mid child_len out.
    abi_native_cursor func cs after counter_inst read_addr (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) ss /\
    counter_inst.inst_id <> target_id /\
    abi_native_memory_ready func (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid source_id target_id source_addr span
      (dst_addr + 32w + mload (w2n dyn_addr) ss) payload
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr length_word ss) /\
    cs_extends (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid /\
    fn_has_code (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid func /\
    abi_native_encoding_result ctx func (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid child_len
      (dst_addr + 32w + mload (w2n dyn_addr) ss) payload
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr length_word ss) out ==>
    abi_native_cursor func cs after counter_inst read_addr mid out /\ mload (w2n read_addr) out = mload (w2n read_addr) ss
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cs`, `dst_addr`, `root_addr`, `width`, `stride`, `counter_addr`, `dyn_addr`, `length_word`, `ss`]
    strip_assume_tac abi_native_dynamic_array_prefix_context >>
  `abi_native_cursor func cs after counter_inst read_addr (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
    (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr length_word ss)` by
    (qspecl_then [`func`, `cs`, `after`, `counter_inst`, `read_addr`, `abi_dynamic_loop_prefix_cut dst src width stride len_op cs`,
       `ss`, `abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
         counter_addr dyn_addr length_word ss`] mp_tac abi_native_cursor_allocator_state >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]) >>
  qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `counter_inst`, `read_addr`,
    `abi_dynamic_loop_prefix_cut dst src width stride len_op cs`,
    `abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr length_word ss`, `mid`, `child_len`, `dst_addr + 32w + mload (w2n dyn_addr) ss`, `payload`, `out`, `target_id`]
    mp_tac abi_native_cursor_static_read >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  drule_all abi_native_result_allocation >> strip_tac >>
  conj_tac
  >- (qspecl_then [`func`, `cs`, `after`, `counter_inst`, `read_addr`, `abi_dynamic_loop_prefix_cut dst src width stride len_op cs`,
       `abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
         counter_addr dyn_addr length_word ss`, `mid`, `out`] mp_tac abi_native_cursor_step >>
      impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [mload_def, read_memory_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual recursive array child counter preservation: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayCallCursor")
