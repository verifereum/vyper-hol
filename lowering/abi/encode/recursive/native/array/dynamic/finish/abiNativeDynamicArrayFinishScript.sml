(* TOP-LEVEL: actual dynamic macro execution and the actual parent
   epilogue complete an enclosing native array result. All recursive
   child runs are obtained from semantic native assertions. *)
Theory abiNativeDynamicArrayFinish
Ancestors
  abiNativeDynamicArrayLoopResult abiNativeDynamicArrayParentEnd abiNativeDynamicArrayFlow abiNativeArrayFinish
  abiNativeTraversal abiNativeTraversalStep abiNativeCursor abiNativeEncodingDefs abiNativeFields abiMemoryLeafRun
  abiDynArrayCode abiDynamicLoopCode abiFieldOperands abiFieldLayoutDefs abiStaticLoopCode
  compileAllocaProvenance compileEnv fragExec venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_finish:
  !ctx func root_cs source_id target_id root_addr source_capacity dst_addr fields initial parent_inst parent_addr parent_ptr
      dst src info width stride len_op cs ret after child_len mid ss reference.
    abi_native_memory_ready func root_cs (abi_dynarray_exit_cut parent_ptr ret after) source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_traversal ctx func root_cs (abi_dynarray_exit_cut parent_ptr ret after) dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial cs ss /\
    abi_native_cursor func root_cs (abi_dynarray_exit_cut parent_ptr ret after) parent_inst parent_addr cs ss /\
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) ss /\
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\ fn_has_code cs after func /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\
    fn_has_code after (abi_dynarray_exit_cut parent_ptr ret after) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\ eval_operand len_op ss = SOME (n2w (LENGTH fields)) /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\ abi_operand_before cs.cs_next_var len_op /\
    eval_operand parent_ptr ss = SOME parent_addr /\ mload (w2n parent_addr) ss = 0w /\ abi_operand_before cs.cs_next_var parent_ptr /\
    32 <= source_capacity /\ LENGTH fields < dimword (:256) /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) (source_capacity - 32) ss.vs_memory fields /\
    mload (w2n root_addr) ss = n2w (LENGTH fields) /\ mload (w2n dst_addr) ss = n2w (LENGTH fields) /\
    abi_native_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) reference fields /\
    mem_bytes_at (w2n root_addr) source_capacity reference = mem_bytes_at (w2n root_addr) source_capacity ss.vs_memory ==>
    ?out. abi_native_encoding_result ctx func root_cs (abi_dynarray_exit_cut parent_ptr ret after)
      (Var (compiler_var_name after.cs_next_var 2)) dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial out
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_native_dynamic_array_loop_result >> disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (qx_choose_then `loop_out` strip_assume_tac) >>
  drule_all abi_native_dynamic_array_parent_end >> strip_tac >>
  `compiler_id_history cs /\ alloca_inv initial` by fs[abi_native_memory_ready_def] >>
  drule_all abi_native_dynamic_array_flow >> strip_tac >>
  `cs_extends after (abi_dynarray_exit_cut parent_ptr ret after)` by simp[abi_dynarray_cuts_extend] >>
  qspecl_then [`ctx`, `func`, `root_cs`, `abi_dynarray_exit_cut parent_ptr ret after`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `initial`, `cs`, `after`, `ret`,
    `dst_addr`, `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `ss`, `loop_out`]
    mp_tac abi_native_traversal_native_step >> impl_tac >- simp[] >> DISCH_TAC >>
  qpat_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def, abi_encoding_result_def]) >>
  qspecl_then [`ctx`, `func`, `root_cs`, `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `initial`,
    `parent_inst`, `parent_addr`, `parent_ptr`, `ret`, `after`, `loop_out`] mp_tac abi_native_array_finish >>
  impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array macro and parent epilogue composition: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayFinish")
