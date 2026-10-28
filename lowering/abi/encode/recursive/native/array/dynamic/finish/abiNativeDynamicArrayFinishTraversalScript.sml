(* TOP-LEVEL: the completed runtime invariant executes the real exit and
   advances its enclosing traversal, preserving the complete allocation
   trace and output/profile frame for the final native result. *)
Theory abiNativeDynamicArrayFinishTraversal
Ancestors
  abiNativeDynamicArrayFinishState abiNativeDynamicArrayParts abiNativeTraversalLoop abiNativeTraversal abiNativeEncodingDefs
  abiDynamicLoopFinish abiDynamicLoopRun abiDynamicLoopCode abiAllocationTrace abiAllocationWindows abiFieldOperands
  abiStaticLoopCode abiBytestringCode compileAllocaProvenance compileEnv fragExec venomState list words arithmetic

Theorem abi_native_dynamic_array_finish_traversal:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr payload initial
      dst src info width stride len_op ret child_len mid ss loop_count counter_addr dyn_addr.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w) payload initial /\
    abi_native_traversal ctx func cs after (dst_addr + 32w) payload initial cs ss /\
    abi_dynamic_loop_ready cs dst src len_op dst_addr root_addr counter_addr dyn_addr loop_count loop_count ss /\
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\ fn_has_code cs after func /\
    abi_operand_before (cs.cs_next_var + 3) src /\ abi_operand_before (cs.cs_next_var + 3) len_op ==>
    abi_native_traversal ctx func cs after (dst_addr + 32w) payload initial cs
      (abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label
        root_addr counter_addr dyn_addr (n2w loop_count) ss)
Proof
  rpt gen_tac >> strip_tac >> `alloca_inv initial` by fs[abi_native_memory_ready_def] >>
  drule_all abi_native_dynamic_array_parts >> strip_tac >>
  qspecl_then [`cs.cs_next_var + 3`, `src`, `cs.cs_next_var + 3`, `3`] mp_tac abi_operand_before_names >>
  impl_tac >- simp[] >>
  simp_tac (srw_ss()) [compiler_var_names_def, GENLIST, compiler_var_name_def, GSYM ADD_ASSOC] >> strip_tac >>
  qspecl_then [`cs.cs_next_var + 3`, `len_op`, `cs.cs_next_var + 3`, `1`] mp_tac abi_operand_before_names >>
  impl_tac >- simp[] >>
  simp_tac (srw_ss()) [compiler_var_names_def, GENLIST, compiler_var_name_def] >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `dst`, `src`, `info`, `width`, `stride`, `len_op`, `cs`, `ret`, `after`, `child_len`, `mid`,
    `ss`, `root_addr`, `counter_addr`, `dyn_addr`, `n2w loop_count`] mp_tac abi_dynamic_loop_finish_path >>
  impl_tac >- fs[abi_dynamic_loop_ready_def, compiler_var_name_def] >> DISCH_TAC >>
  qspecl_then [`mid`, `cs`, `root_addr`, `counter_addr`, `dyn_addr`, `n2w loop_count`, `ss`]
    strip_assume_tac abi_native_dynamic_array_finish_context >>
  `abi_allocation_trace 32 (compiler_alloca_ids cs after) ss
    (abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label root_addr counter_addr dyn_addr (n2w loop_count) ss)` by
    (irule abi_allocation_trace_identity >> first_assum MATCH_ACCEPT_TAC) >>
  `abi_memory_frame ((w2n (dst_addr + 32w),LENGTH payload)::abi_allocation_windows (compiler_alloca_ids cs after)
    (abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label root_addr counter_addr dyn_addr (n2w loop_count) ss)) ss
    (abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label root_addr counter_addr dyn_addr (n2w loop_count) ss)` by
    (irule abi_memory_frame_subset >> qexists_tac `[]` >> simp[]) >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==>
    eval_operand arg_op (abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label
      root_addr counter_addr dyn_addr (n2w loop_count) ss) = eval_operand arg_op ss` by
    (rpt gen_tac >> DISCH_TAC >> irule abi_native_dynamic_array_finish_old_operand >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >> irule abi_operand_before_mono >>
     qexists_tac `cs.cs_next_var` >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `dst_addr + 32w`, `payload`, `initial`, `cs`, `ss`,
    `abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label root_addr counter_addr dyn_addr (n2w loop_count) ss`]
    mp_tac abi_native_traversal_runtime_step >> impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual completed array exit traversal: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayFinishTraversal")
