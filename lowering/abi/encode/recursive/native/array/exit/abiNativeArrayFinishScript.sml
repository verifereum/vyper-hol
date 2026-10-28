(* TOP-LEVEL: the actual parent epilogue completes the whole native array
   execution, retaining the original traversal's path, scratch and allocation
   trace rather than assuming an epilogue execution contract. *)
Theory abiNativeArrayFinish
Ancestors
  abiNativeArrayExitResult abiNativeArrayExitState abiNativeArrayBudget abiNativeTraversal abiNativeTraversalStep
  abiNativeCursor abiNativeEncodingDefs abiMemoryLeafRun abiDynArrayCode abiAllocationTrace abiAllocationWindows
  abiAllocatorState abiMemoryFrame abiFieldOperands compileIdFlow compileAllocaProvenance compileEnv fragExec
  venomMemDefs venomState list words arithmetic

Theorem abi_native_array_finish:
  !ctx func root_cs source_id target_id root_addr source_capacity dst_addr payload initial parent_inst parent_addr
      parent_ptr encoded_size cs ss.
    abi_native_memory_ready func root_cs (abi_dynarray_exit_cut parent_ptr encoded_size cs)
      source_id target_id root_addr source_capacity dst_addr payload initial /\
    abi_native_traversal ctx func root_cs (abi_dynarray_exit_cut parent_ptr encoded_size cs)
      dst_addr payload initial cs ss /\
    abi_native_cursor func root_cs (abi_dynarray_exit_cut parent_ptr encoded_size cs) parent_inst parent_addr cs ss /\
    fn_has_code cs (abi_dynarray_exit_cut parent_ptr encoded_size cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand parent_ptr ss = SOME parent_addr /\ eval_operand encoded_size ss = SOME (n2w (LENGTH payload)) /\
    mload (w2n parent_addr) ss = 0w /\ read_memory (w2n dst_addr) (LENGTH payload) ss = payload /\
    abi_operand_before cs.cs_next_var parent_ptr /\ abi_operand_before cs.cs_next_var encoded_size ==>
    ?out. abi_native_encoding_result ctx func root_cs (abi_dynarray_exit_cut parent_ptr encoded_size cs)
      (Var (compiler_var_name cs.cs_next_var 2)) dst_addr payload initial out
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_traversal_root_ready >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `root_cs`, `abi_dynarray_exit_cut parent_ptr encoded_size cs`,
    `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`, `payload`, `parent_inst`, `parent_addr`,
    `parent_ptr`, `encoded_size`, `cs`, `ss`] mp_tac abi_native_array_exit_result >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qabbrev_tac `out = abi_native_array_exit_boundary cs parent_addr (n2w (LENGTH payload)) ss` >>
  `abi_allocation_trace 32 (compiler_alloca_ids cs (abi_dynarray_exit_cut parent_ptr encoded_size cs)) ss out` by
    (irule abi_allocation_trace_identity >> asm_simp_tac bool_ss [Abbr`out`]) >>
  `compiler_id_history cs /\ alloca_inv initial` by fs[abi_native_traversal_def, abi_native_memory_ready_def] >>
  `compiler_id_history (abi_dynarray_exit_cut parent_ptr encoded_size cs)` by simp[abi_native_array_exit_history] >>
  `cs_extends cs (abi_dynarray_exit_cut parent_ptr encoded_size cs) /\
    cs.cs_next_var <= (abi_dynarray_exit_cut parent_ptr encoded_size cs).cs_next_var` by
    simp[abi_dynarray_cuts_extend, abi_dynarray_exit_cut_def] >>
  `abi_native_traversal ctx func root_cs (abi_dynarray_exit_cut parent_ptr encoded_size cs)
    dst_addr payload initial (abi_dynarray_exit_cut parent_ptr encoded_size cs) out` by
    (qspecl_then [`ctx`, `func`, `root_cs`, `abi_dynarray_exit_cut parent_ptr encoded_size cs`, `dst_addr`, `payload`,
       `initial`, `cs`, `abi_dynarray_exit_cut parent_ptr encoded_size cs`, `Var (compiler_var_name cs.cs_next_var 2)`,
       `dst_addr`, `payload`, `abi_allocation_windows (compiler_alloca_ids root_cs (abi_dynarray_exit_cut parent_ptr encoded_size cs)) out`,
       `ss`, `out`] mp_tac abi_native_traversal_step >>
     impl_tac >- fs[Abbr`out`, abi_encoding_result_def, cs_extends_refl] >> simp_tac bool_ss []) >>
  qpat_x_assum `abi_native_traversal _ _ _ _ _ _ _ _ out`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  qpat_x_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  qexists_tac `out` >> PURE_REWRITE_TAC [abi_native_encoding_result_def, abi_encoding_result_def] >>
  asm_simp_tac bool_ss [Abbr`out`]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native array final composition: " ^ name)
  end) (DB.thms "abiNativeArrayFinish")
