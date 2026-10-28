(* TOP-LEVEL: owned parent setup produces the actual parent pointer,
   saved array length, output header and zero parent word. Whole-source
   observation follows from the proved enclosing traversal frame. *)
Theory abiNativeArrayParentValues
Ancestors
  abiNativeArrayParentReady abiNativeArrayReadFrame abiNativeCursor abiNativeTraversal abiNativeTraversalReady
  abiNativeEncodingDefs abiDynArrayBoundaryFrames abiDynArrayCode abiStaticLoopCode abiAllocatedWindows
  abiMemoryEncodingFrame memoryReadProps valueEncodingProofs compileAllocaProvenance compileEnv venomMemDefs venomState list words

Theorem abi_native_array_parent_values:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr payload ss dst src parent_inst length_word.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity dst_addr payload ss /\
    abi_native_traversal ctx func cs after dst_addr payload ss (abi_dynarray_entry_cut dst src cs)
      (abi_dynarray_entry_boundary cs dst_addr root_addr ss) /\
    abi_native_cursor func cs after parent_inst (abi_static_loop_counter_addr cs.cs_next_id ss)
      (abi_dynarray_entry_cut dst src cs) (abi_dynarray_entry_boundary cs dst_addr root_addr ss) /\
    32 <= source_capacity /\ 32 <= LENGTH payload /\ mload (w2n root_addr) ss = length_word ==>
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) (abi_dynarray_entry_boundary cs dst_addr root_addr ss) =
      SOME (abi_static_loop_counter_addr cs.cs_next_id ss) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1)) (abi_dynarray_entry_boundary cs dst_addr root_addr ss) =
      SOME length_word /\
    mload (w2n dst_addr) (abi_dynarray_entry_boundary cs dst_addr root_addr ss) = length_word /\
    mload (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) (abi_dynarray_entry_boundary cs dst_addr root_addr ss) = 0w /\
    mload (w2n root_addr) (abi_dynarray_entry_boundary cs dst_addr root_addr ss) = length_word
Proof
  rpt gen_tac >> strip_tac >>
  `alloca_inv ss /\ ~MEM source_id (compiler_alloca_ids cs after) /\ ~MEM target_id (compiler_alloca_ids cs after)` by
    fs[abi_native_memory_ready_def] >>
  drule_all abi_native_traversal_allocation >> strip_tac >>
  drule_all abi_native_traversal_windows >> strip_tac >>
  qspecl_then [`func`, `cs`, `after`, `parent_inst`, `abi_static_loop_counter_addr cs.cs_next_id ss`,
    `abi_dynarray_entry_cut dst src cs`, `abi_dynarray_entry_boundary cs dst_addr root_addr ss`, `source_id`, `target_id`]
    mp_tac abi_native_cursor_root_distinct >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_native_cursor _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  qspecl_then [`abi_dynarray_entry_boundary cs dst_addr root_addr ss`, `source_id`, `target_id`, `parent_inst.inst_id`,
    `w2n root_addr`, `source_capacity`, `w2n dst_addr`, `LENGTH payload`,
    `w2n (abi_static_loop_counter_addr cs.cs_next_id ss)`] mp_tac abi_native_array_parent_regions >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`cs`, `dst_addr`, `root_addr`, `abi_static_loop_counter_addr cs.cs_next_id ss`, `length_word`, `ss`]
    mp_tac abi_dynarray_entry_boundary_values >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_native_traversal_source >> DISCH_TAC >>
  qspecl_then [`w2n root_addr`, `source_capacity`, `ss.vs_memory`,
    `(abi_dynarray_entry_boundary cs dst_addr root_addr ss).vs_memory`] mp_tac abi_memory_window_header >>
  impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >> sym_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `mload (w2n root_addr) (abi_dynarray_entry_boundary cs dst_addr root_addr ss) = length_word` by
    fs[mem_word_at_eq_mload_proof] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed owned native array parent pointer/header values: " ^ name)
  end) (DB.thms "abiNativeArrayParentValues")
