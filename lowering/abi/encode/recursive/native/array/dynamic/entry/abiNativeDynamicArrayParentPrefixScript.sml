(* TOP-LEVEL: the actual outer parent prefix supplies the dynamic macro's
   resources, original raw source, saved length and zero parent cell. *)
Theory abiNativeDynamicArrayParentPrefix
Ancestors
  abiNativeArrayParentReady abiNativeArrayParentValues abiNativeArrayEntryOperands abiNativeArraySource abiNativeResources
  abiNativeTraversal abiNativeCursor abiNativeEncodingDefs abiDynArrayCode abiDynArrayBoundaryFrames abiStaticLoopEntry
  abiFieldOperands abiFieldLayoutDefs compileAllocaProvenance compileEnv fragExec venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_parent_prefix:
  !ctx func cs root_after source_id target_id root_addr source_capacity dst_addr fields info width stride initial dst src loop_after.
    abi_native_memory_ready func cs root_after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    32 <= source_capacity /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) (source_capacity - 32) initial.vs_memory fields /\
    mload (w2n root_addr) initial = n2w (LENGTH fields) /\
    fn_has_code cs (abi_dynarray_entry_cut dst src cs) func /\ cs_extends (abi_dynarray_entry_cut dst src cs) root_after /\
    cs_extends loop_after root_after /\ abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    eval_operand dst initial = SOME dst_addr /\ eval_operand src initial = SOME root_addr /\
    initial.vs_current_bb = cs.cs_current_bb /\ initial.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~initial.vs_halted ==>
    let macro = abi_dynarray_entry_cut dst src cs in
    let current = abi_dynarray_entry_boundary cs dst_addr root_addr initial in
    abi_native_traversal ctx func cs root_after dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial macro current /\
    abi_native_cursor func cs root_after (abi_native_array_counter_inst cs) (abi_static_loop_counter_addr cs.cs_next_id initial) macro current /\
    abi_native_memory_ready func macro loop_after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) current /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) (source_capacity - 32) current.vs_memory fields /\
    mload (w2n root_addr) current = n2w (LENGTH fields) /\ mload (w2n dst_addr) current = n2w (LENGTH fields) /\
    eval_operand dst current = SOME dst_addr /\ eval_operand src current = SOME root_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) current = SOME (abi_static_loop_counter_addr cs.cs_next_id initial) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1)) current = SOME (n2w (LENGTH fields)) /\
    mload (w2n (abi_static_loop_counter_addr cs.cs_next_id initial)) current = 0w /\
    current.vs_current_bb = macro.cs_current_bb /\ current.vs_inst_idx = LENGTH macro.cs_current_insts /\ ~current.vs_halted /\
    EVERY (abi_operand_before macro.cs_next_var) [dst;src;Var (compiler_var_name cs.cs_next_var 0);Var (compiler_var_name cs.cs_next_var 1)] /\
    mem_bytes_at (w2n root_addr) source_capacity current.vs_memory = mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cs`, `root_after`, `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `initial`, `dst`, `src`,
    `abi_native_array_counter_inst cs`] mp_tac abi_native_array_parent_traversal >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_native_array_counter_inst_def] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cs`, `root_after`, `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `initial`, `dst`, `src`,
    `abi_native_array_counter_inst cs`, `n2w (LENGTH fields)`]
    mp_tac abi_native_array_parent_values >> impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`cs`, `dst`, `src`, `dst_addr`, `root_addr`, `initial`] mp_tac abi_native_array_parent_control >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`cs`, `dst`, `src`, `dst_addr`, `root_addr`, `initial`] mp_tac abi_native_array_parent_operands >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cs`, `root_after`, `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `initial`,
    `abi_dynarray_entry_cut dst src cs`, `abi_dynarray_entry_boundary cs dst_addr root_addr initial`,
    `REPLICATE (LENGTH fields) (info,width,stride,T)`, `fields`, `n2w (LENGTH fields)`]
    mp_tac abi_native_array_source >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_native_traversal_source >> DISCH_TAC >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  qspecl_then [`func`, `cs`, `root_after`, `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `initial`,
    `abi_dynarray_entry_cut dst src cs`, `loop_after`, `abi_dynarray_entry_boundary cs dst_addr root_addr initial`,
    `root_addr`, `source_capacity`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`]
    mp_tac abi_native_child_ready >> impl_tac >- simp[] >> DISCH_TAC >>
  qspecl_then [`cs.cs_next_var`, `(abi_dynarray_entry_cut dst src cs).cs_next_var`, `dst`, `src`]
    mp_tac abi_native_array_operands_before >> impl_tac >- simp[abi_dynarray_entry_cut_def] >> DISCH_TAC >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array parent prefix resources and values: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayParentPrefix")
