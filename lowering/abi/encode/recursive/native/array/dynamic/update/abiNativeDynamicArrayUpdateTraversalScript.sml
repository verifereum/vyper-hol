(* TOP-LEVEL: the actual compiled post-child path advances the enclosing
   traversal across its stores and latch, then selects the loop context
   again for the next visit to the same generated code. *)
Theory abiNativeDynamicArrayUpdateTraversal
Ancestors
  abiNativeDynamicArrayUpdatePath abiNativeDynamicArrayUpdateFrame abiNativeDynamicArrayUpdateState
  abiNativeTraversalLoop abiNativeTraversal abiNativeEncodingDefs abiNativeCursor abiAllocationTrace abiFieldOperands
  abiDynamicLoopIteration abiDynamicLoopCode compileAllocaProvenance compileEnv fragExec venomState venomInst list words

Theorem abi_native_dynamic_array_next_traversal:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr payload initial
      dst src info width stride len_op ret child_len mid ss index counter_addr dyn_addr tail_offset child_size dyn_inst index_inst.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w) payload initial /\
    abi_native_traversal ctx func cs after (dst_addr + 32w) payload initial mid ss /\
    abi_native_cursor func cs after dyn_inst dyn_addr mid ss /\ abi_native_cursor func cs after index_inst counter_addr mid ss /\
    w2n (dst_addr + 32w) <= w2n (dst_addr + 32w + n2w index * n2w width) /\
    w2n (dst_addr + 32w + n2w index * n2w width) + 32 <= w2n (dst_addr + 32w) + LENGTH payload /\
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\ fn_has_code cs after func /\
    abi_dynamic_loop_child_return cs.cs_next_var mid child_len dst_addr width counter_addr dyn_addr
      (n2w index) tail_offset child_size ss ==>
    abi_native_traversal ctx func cs after (dst_addr + 32w) payload initial cs
      (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss)
Proof
  rpt gen_tac >> strip_tac >>
  `alloca_inv initial /\ compiler_id_history cs` by fs[abi_native_memory_ready_def] >>
  `cs.cs_next_var <= mid.cs_next_var` by fs[abi_native_traversal_def] >>
  drule_all abi_native_dynamic_array_next_path >> DISCH_TAC >>
  qspecl_then [`cs`, `mid`, `dst_addr`, `width`, `counter_addr`, `dyn_addr`, `index`, `tail_offset`, `child_size`, `ss`]
    strip_assume_tac abi_native_dynamic_array_next_frame >>
  qspecl_then [`func`, `cs`, `after`, `cs`, `mid`, `dst_addr`, `width`, `counter_addr`, `dyn_addr`, `index`,
    `tail_offset`, `child_size`, `ss`, `dyn_inst`, `index_inst`, `dst_addr + 32w`, `payload`]
    mp_tac abi_native_dynamic_array_next_cursor_frame >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_allocation_trace 32 (compiler_alloca_ids cs after) ss
    (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss)` by
    (irule abi_allocation_trace_identity >> first_assum MATCH_ACCEPT_TAC) >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==>
    eval_operand arg_op (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss) =
      eval_operand arg_op ss` by
    (rpt gen_tac >> DISCH_TAC >> irule abi_native_dynamic_array_next_old_operand >>
     irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> asm_simp_tac bool_ss []) >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `dst_addr + 32w`, `payload`, `initial`, `mid`, `ss`,
    `abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss`]
    mp_tac abi_native_traversal_runtime_step >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `dst_addr + 32w`, `payload`, `initial`, `mid`,
    `abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss`, `cs`]
    mp_tac abi_native_traversal_context >> impl_tac >- simp[cs_extends_refl] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual post-child array traversal and compiler backedge: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayUpdateTraversal")
