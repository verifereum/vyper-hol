(* TOP-LEVEL: a complete actual macro retains the enclosing parent cell
   and operand. Its returned byte count precedes the final SSA frontier
   and is ready for the real parent epilogue. *)
Theory abiNativeDynamicArrayParentEnd
Ancestors
  abiNativeDynamicArrayFlow abiNativeCursorFrame abiNativeCursor abiNativeArrayBudget abiNativeResources
  abiNativeTraversal abiNativeEncodingDefs abiMemoryLeafRun abiDynamicLoopFactor abiDynamicLoopCode abiChildCode
  abiFieldOperands abiAllocatedWindows abiStaticLoopCode compileAllocaProvenance compileEnv fragExec
  venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_loop_result_before:
  !dst src info width stride len_op cs ret after child_len mid.
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) ==>
    abi_operand_before after.cs_next_var ret
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_abi_dynamic_loop_factor, LET_THM, abi_dynamic_loop_exit_cut_def, abi_dynamic_loop_latch_cut_def,
    abi_child_suffix_cut_def, abi_operand_before_def, compiler_var_name_def] >> rpt strip_tac >> decide_tac
QED

Theorem abi_native_dynamic_array_parent_end:
  !ctx func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload initial
      parent_inst parent_addr parent_ptr dst src info width stride len_op cs ret after child_len mid ss out.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr payload initial cs ss /\
    abi_native_cursor func root_cs root_after parent_inst parent_addr cs ss /\
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\ fn_has_code cs after func /\
    abi_native_encoding_result ctx func cs after ret dst_addr payload ss out /\ abi_operand_before cs.cs_next_var parent_ptr ==>
    abi_native_cursor func root_cs root_after parent_inst parent_addr after out /\
    mload (w2n parent_addr) out = mload (w2n parent_addr) ss /\ eval_operand parent_ptr out = eval_operand parent_ptr ss /\
    abi_operand_before after.cs_next_var parent_ptr /\ abi_operand_before after.cs_next_var ret
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_traversal_root_ready >> DISCH_TAC >>
  `compiler_id_history cs` by fs[abi_native_traversal_def] >>
  drule_all abi_native_dynamic_array_flow >> strip_tac >>
  `fn_inst_ids_distinct func /\ alloca_inv ss /\ ~MEM source_id (compiler_alloca_ids root_cs root_after) /\
    ~MEM target_id (compiler_alloca_ids root_cs root_after) /\ abi_allocated_window ss target_id (w2n dst_addr) (LENGTH payload)` by
    fs[abi_native_memory_ready_def] >>
  qspecl_then [`func`, `root_cs`, `root_after`, `parent_inst`, `parent_addr`, `cs`, `ss`, `source_id`, `target_id`]
    mp_tac abi_native_cursor_root_distinct >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `root_cs`, `root_after`, `parent_inst`, `parent_addr`, `cs`, `ss`, `after`, `ret`,
    `dst_addr`, `payload`, `out`, `target_id`] mp_tac abi_native_cursor_static_read >>
  impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  drule_all abi_native_result_allocation >> strip_tac >>
  qspecl_then [`func`, `root_cs`, `root_after`, `parent_inst`, `parent_addr`, `cs`, `ss`, `after`, `out`]
    mp_tac abi_native_cursor_step >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qpat_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def, abi_encoding_result_def]) >>
  `eval_operand parent_ptr out = eval_operand parent_ptr ss` by
    (first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  `abi_operand_before after.cs_next_var parent_ptr` by
    (irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> asm_simp_tac bool_ss []) >>
  drule_all abi_native_dynamic_array_loop_result_before >> DISCH_TAC >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed completed dynamic array parent cell and operand preservation: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayParentEnd")
