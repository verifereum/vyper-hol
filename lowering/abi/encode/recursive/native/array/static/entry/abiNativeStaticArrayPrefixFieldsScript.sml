(* TOP-LEVEL: actual parent/index prefix execution initializes the complete
   static-array header assertion, including raw fields, both owned cells,
   control position and every operand consumed by the generated loop. *)
Theory abiNativeStaticArrayPrefixFields
Ancestors
  abiNativeStaticArrayEntry abiNativeStaticArrayHeader abiNativeArrayEntryOperands abiNativeArrayParentValues
  abiNativeStaticStartMemory abiNativeStaticParentStart abiNativeStaticStartOperands abiNativeStaticStartState
  abiNativeStaticHeaderCode abiNativeTraversal abiNativeCursor abiNativeEncodingDefs abiDynArrayCode abiDynArrayBoundaryFrames
  abiStaticLoopEntry abiStaticLoopCode abiFieldOperands compileIdFlow compileEnv fragExec venomMemDefs venomState list words arithmetic

Theorem abi_native_static_array_prefix_fields:
  !ctx func cs root_after source_id target_id root_addr source_capacity dst_addr fields initial dst src info stride ret after.
    abi_native_memory_ready func cs root_after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    32 <= source_capacity /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,abi_static_encoder_size info,stride,F))
      (w2n root_addr + 32) (source_capacity - 32) initial.vs_memory fields /\
    mload (w2n root_addr) initial = n2w (LENGTH fields) /\
    compile_abi_encode_dyn_static_loop dst src info (abi_static_encoder_size info) stride
      (Var (compiler_var_name cs.cs_next_var 1)) (abi_dynarray_entry_cut dst src cs) = (ret,after) /\
    fn_has_code cs (abi_dynarray_entry_cut dst src cs) func /\
    fn_has_code (abi_dynarray_entry_cut dst src cs) after func /\ cs_extends after root_after /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    eval_operand dst initial = SOME dst_addr /\ eval_operand src initial = SOME root_addr /\
    initial.vs_current_bb = cs.cs_current_bb /\ initial.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~initial.vs_halted ==>
    abi_native_static_array_header ctx func cs root_after dst src root_addr source_capacity dst_addr info stride fields initial
      (abi_native_static_array_start cs dst src dst_addr root_addr initial)
Proof
  rpt gen_tac >> strip_tac >>
  `32 <= LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)` by simp[] >>
  drule_all abi_native_static_array_prefix_traversal >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [abi_native_static_array_start_def, LET_THM]) >>
  qspecl_then [`ctx`, `func`, `cs`, `root_after`, `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`,
    `initial`, `dst`, `src`, `abi_native_array_counter_inst cs`, `n2w (LENGTH fields)`]
    mp_tac abi_native_array_parent_values >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`cs`, `dst`, `src`, `dst_addr`, `root_addr`, `initial`]
    mp_tac abi_native_array_parent_control >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`cs`, `dst`, `src`, `dst_addr`, `root_addr`, `initial`]
    mp_tac abi_native_array_parent_operands >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cs`, `root_after`, `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`,
    `fields`, `info`, `abi_static_encoder_size info`, `stride`, `initial`, `abi_dynarray_entry_cut dst src cs`,
    `abi_dynarray_entry_boundary cs dst_addr root_addr initial`, `abi_native_array_counter_inst (abi_dynarray_entry_cut dst src cs)`]
    mp_tac abi_native_static_start_data >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `alloca_inv initial` by fs[abi_native_memory_ready_def] >>
  qspecl_then [`ctx`, `func`, `cs`, `root_after`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `initial`,
    `abi_dynarray_entry_cut dst src cs`, `abi_dynarray_entry_boundary cs dst_addr root_addr initial`]
    mp_tac abi_native_traversal_allocation >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cs`, `root_after`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `initial`,
    `abi_native_static_header_cut (abi_dynarray_entry_cut dst src cs)`,
    `abi_static_loop_start_state (abi_dynarray_entry_cut dst src cs).cs_next_id (abi_dynarray_entry_cut dst src cs).cs_next_var
      (abi_dynarray_entry_cut dst src cs).cs_next_label (abi_dynarray_entry_boundary cs dst_addr root_addr initial)`]
    mp_tac abi_native_traversal_allocation >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `(abi_native_array_counter_inst cs).inst_id <> (abi_native_array_counter_inst (abi_dynarray_entry_cut dst src cs)).inst_id` by
    simp[abi_dynarray_entry_cut_def] >>
  qspecl_then [`ctx`, `func`, `cs`, `root_after`, `abi_native_array_counter_inst cs`, `abi_static_loop_counter_addr cs.cs_next_id initial`,
    `abi_native_array_counter_inst (abi_dynarray_entry_cut dst src cs)`, `dst`, `src`, `info`, `abi_static_encoder_size info`,
    `stride`, `Var (compiler_var_name cs.cs_next_var 1)`, `abi_dynarray_entry_cut dst src cs`, `ret`, `after`,
    `abi_dynarray_entry_boundary cs dst_addr root_addr initial`] mp_tac abi_native_static_parent_start >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`cs.cs_next_var`, `abi_dynarray_entry_cut dst src cs`, `dst`, `src`, `dst_addr`, `root_addr`,
    `abi_static_loop_counter_addr cs.cs_next_id initial`, `n2w (LENGTH fields)`, `abi_dynarray_entry_boundary cs dst_addr root_addr initial`]
    mp_tac abi_native_static_start_operands >> impl_tac >- asm_simp_tac (srw_ss()) [abi_dynarray_entry_cut_def] >> strip_tac >>
  qspecl_then [`abi_dynarray_entry_cut dst src cs`, `abi_dynarray_entry_boundary cs dst_addr root_addr initial`]
    strip_assume_tac abi_native_static_start_context >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ (abi_dynarray_entry_cut dst src cs) _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  fs[abi_native_static_array_header_def, abi_native_static_array_start_def, LET_THM, abi_native_static_header_cut_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete actual static array prefix/header initialization: " ^ name)
  end) (DB.thms "abiNativeStaticArrayPrefixFields")
