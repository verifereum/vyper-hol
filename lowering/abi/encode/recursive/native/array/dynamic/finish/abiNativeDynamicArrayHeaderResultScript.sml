(* TOP-LEVEL: from the real initial header, semantic recursive children
   execute the entire runtime loop and its actual exit. The native result
   contains the complete length-prefixed array bytes and allocation trace. *)
Theory abiNativeDynamicArrayHeaderResult
Ancestors
  abiNativeDynamicArrayRepeat abiNativeDynamicArrayInvariant abiNativeDynamicArrayState abiNativeDynamicArrayFinishTraversal
  abiNativeDynamicArrayFinishState abiNativeTraversalResult abiNativeTraversal abiNativeEncodingDefs abiNativeFields
  abiDynamicLoopFinish abiDynamicLoopFactor abiDynamicLoopCode abiChildCode abiDynamicLoopRun abiFieldOperands
  abiFieldLayoutDefs abiAllocatedWindows abiStaticLoopCode compileEnv fragExec venomMemDefs venomState venomInst list words arithmetic

Theorem abi_native_dynamic_array_header_result:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride initial reference
      dst src len_op ret mid child_len counter_addr dyn_addr dyn_inst index_inst.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_dynamic_array_invariant ctx func cs after dst src len_op dst_addr root_addr counter_addr dyn_addr
      info width stride fields source_capacity initial dyn_inst index_inst 0 initial /\
    abi_allocated_window initial target_id (w2n dst_addr) 32 /\
    abi_native_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) reference fields /\
    mem_bytes_at (w2n root_addr) source_capacity reference = mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\ fn_has_code cs after func /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\
    dyn_inst.inst_id <> index_inst.inst_id /\ w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ LENGTH fields < dimword (:256) /\
    abi_operand_before (cs.cs_next_var + 3) dst /\ abi_operand_before (cs.cs_next_var + 3) src /\
    abi_operand_before (cs.cs_next_var + 3) len_op ==>
    ?out. abi_native_encoding_result ctx func cs after ret dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial out
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_native_dynamic_array_repeat >> disch_then (qx_choose_then `boundary` strip_assume_tac) >>
  qpat_assum `abi_native_dynamic_array_invariant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ boundary`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_dynamic_array_invariant_def]) >>
  drule_all abi_native_dynamic_array_finish_traversal >> DISCH_TAC >>
  qspecl_then [`mid.cs_next_var`, `cs.cs_next_var`, `cs.cs_next_label`, `root_addr`, `counter_addr`, `dyn_addr`, `n2w (LENGTH fields)`, `boundary`]
    mp_tac abi_dynamic_loop_finish_values >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `ret = Var (compiler_var_name (mid.cs_next_var + 2) 2) /\
    after.cs_current_bb = fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2) /\ LENGTH after.cs_current_insts = 3` by
    gvs[compile_abi_dynamic_loop_factor, LET_THM, abi_dynamic_loop_exit_cut_def,
      abi_dynamic_loop_latch_cut_def, abi_child_suffix_cut_def] >>
  qspecl_then [`info`, `width`, `stride`, `fields`, `dst_addr`, `root_addr`, `counter_addr`, `dyn_addr`, `source_capacity`, `boundary`]
    mp_tac abi_native_dynamic_array_complete >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  `abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity (LENGTH fields)
    (abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label root_addr counter_addr dyn_addr (n2w (LENGTH fields)) boundary)` by
    (qspecl_then [`info`, `width`, `stride`, `fields`, `dst_addr`, `root_addr`, `counter_addr`, `dyn_addr`, `source_capacity`,
       `LENGTH fields`, `boundary`,
       `abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label root_addr counter_addr dyn_addr (n2w (LENGTH fields)) boundary`]
       mp_tac abi_native_dynamic_array_data_memory >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]) >>
  qspecl_then [`info`, `width`, `stride`, `fields`, `dst_addr`, `root_addr`, `counter_addr`, `dyn_addr`, `source_capacity`,
    `abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label root_addr counter_addr dyn_addr (n2w (LENGTH fields)) boundary`]
    mp_tac abi_native_dynamic_array_complete >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  qexists_tac `abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label
    root_addr counter_addr dyn_addr (n2w (LENGTH fields)) boundary` >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `dst_addr + 32w`, `abi_field_bytes (abi_field_head_size fields) fields`, `initial`, `cs`,
    `abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label root_addr counter_addr dyn_addr (n2w (LENGTH fields)) boundary`,
    `ret`, `dst_addr`, `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`]
    mp_tac abi_native_traversal_result >>
  impl_tac >- (asm_simp_tac (srw_ss()) [word_add_n2w] >> decide_tac) >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual full dynamic array header loop and exit native result: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayHeaderResult")
