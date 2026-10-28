(* TOP-LEVEL: actual setup establishes the two cursors used by every
   dynamic-array iteration, backed by the real allocation instructions
   and the enclosing compiler's physical allocation budget. *)
Theory abiNativeDynamicArrayStartCursors
Ancestors
  abiNativeDynamicArrayStartCode abiNativeDynamicArrayStartState abiNativeDynamicArrayStartWindows abiNativeCursor
  abiNativeEncodingDefs abiAllocatedWindows abiAllocationBudget abiAllocationFrame abiDynamicLoopCode abiStaticLoopEntry
  abiStaticLoopCode compileAllocaProvenance compileEnv fragExec venomMemDefs venomState venomInst list words arithmetic

Theorem abi_native_dynamic_array_start_cursors:
  !func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload ss
      dst src info width stride len_op cs ret after child_len mid length_word.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload ss /\
    cs_extends root_cs cs /\ compiler_id_history cs /\
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\
    fn_has_code cs after func /\ cs_extends after root_after ==>
    abi_native_cursor func root_cs root_after (abi_native_dynamic_array_index_inst cs)
      (abi_static_loop_counter_addr cs.cs_next_id ss) (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
      (abi_native_dynamic_array_start_state cs width length_word ss) /\
    abi_native_cursor func root_cs root_after (abi_native_dynamic_array_tail_inst cs)
      (abi_native_dynamic_array_tail_addr cs ss) (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
      (abi_native_dynamic_array_start_state cs width length_word ss)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`root_cs`, `root_after`, `dst`, `src`, `info`, `width`, `stride`, `len_op`, `cs`, `ret`, `after`, `child_len`, `mid`,
    `func`, `abi_native_dynamic_array_index_inst cs`] mp_tac abi_native_dynamic_array_start_provenance >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`root_cs`, `root_after`, `dst`, `src`, `info`, `width`, `stride`, `len_op`, `cs`, `ret`, `after`, `child_len`, `mid`,
    `func`, `abi_native_dynamic_array_tail_inst cs`] mp_tac abi_native_dynamic_array_start_provenance >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
  `MEM cs.cs_next_id (compiler_alloca_ids root_cs root_after) /\ MEM (cs.cs_next_id + 2) (compiler_alloca_ids root_cs root_after)` by
    fs[abi_native_dynamic_array_index_inst_def, abi_native_dynamic_array_tail_inst_def, mk_inst_def] >>
  `abi_alloca_request_ok cs.cs_next_id 32 ss /\ abi_alloca_request_ok (cs.cs_next_id + 2) 32 ss` by
    (conj_tac >> first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`cs`, `width`, `length_word`, `compiler_alloca_ids root_cs root_after`, `ss`]
    mp_tac abi_native_dynamic_array_start_windows >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  PURE_REWRITE_TAC [abi_native_cursor_def] >> rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac (srw_ss()) [abi_native_dynamic_array_index_inst_def, abi_native_dynamic_array_tail_inst_def, mk_inst_def]]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array setup owned cursors: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayStartCursors")
