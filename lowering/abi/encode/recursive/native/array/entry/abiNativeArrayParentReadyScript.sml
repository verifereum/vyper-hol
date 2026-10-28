(* TOP-LEVEL: the actual parent-cell prefix establishes its owned cursor
   and the enclosing native traversal invariant from computed-profile
   allocation resources. Both fresh allocation and cached replay apply. *)
Theory abiNativeArrayParentReady
Ancestors
  abiNativeArrayParentCode abiNativeArrayParentState abiNativeArrayParentFrame
  abiNativeCursor abiNativeTraversal abiNativeEncodingDefs abiDynArrayCode abiDynArrayBoundaryFrames abiStaticLoopCode
  abiAllocationWindows abiAllocationBudget abiAllocationFrame abiFieldOperands abiMemoryFrame abiStateFrame
  compileAllocaProvenance compileIdFlow compileEnv fragExec venomMemDefs venomState venomInst list words arithmetic

Theorem abi_native_array_parent_cursor:
  !func cs after parent_inst dst src dst_addr root_addr ss.
    parent_inst = mk_inst cs.cs_next_id ALLOCA [Lit 32w] [compiler_var_name cs.cs_next_var 0] /\
    compiler_id_history cs /\ fn_has_code cs (abi_dynarray_entry_cut dst src cs) func /\
    cs_extends (abi_dynarray_entry_cut dst src cs) after /\
    abi_allocated_window (abi_dynarray_entry_boundary cs dst_addr root_addr ss) cs.cs_next_id
      (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) 32 ==>
    abi_native_cursor func cs after parent_inst (abi_static_loop_counter_addr cs.cs_next_id ss)
      (abi_dynarray_entry_cut dst src cs) (abi_dynarray_entry_boundary cs dst_addr root_addr ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_array_parent_provenance >> strip_tac >>
  simp_tac bool_ss [abi_native_cursor_def] >> asm_simp_tac (srw_ss()) [mk_inst_def]
QED

Theorem abi_native_array_parent_traversal:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr payload ss dst src parent_inst.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity dst_addr payload ss /\
    32 <= LENGTH payload /\
    parent_inst = mk_inst cs.cs_next_id ALLOCA [Lit 32w] [compiler_var_name cs.cs_next_var 0] /\
    fn_has_code cs (abi_dynarray_entry_cut dst src cs) func /\ cs_extends (abi_dynarray_entry_cut dst src cs) after /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    abi_native_traversal ctx func cs after dst_addr payload ss (abi_dynarray_entry_cut dst src cs)
      (abi_dynarray_entry_boundary cs dst_addr root_addr ss) /\
    abi_native_cursor func cs after parent_inst (abi_static_loop_counter_addr cs.cs_next_id ss)
      (abi_dynarray_entry_cut dst src cs) (abi_dynarray_entry_boundary cs dst_addr root_addr ss)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
  drule_all abi_native_array_parent_provenance >> strip_tac >>
  `MEM cs.cs_next_id (compiler_alloca_ids cs after)` by gvs[mk_inst_def] >>
  `abi_alloca_request_ok cs.cs_next_id 32 ss` by (first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`cs`, `dst_addr`, `root_addr`, `compiler_alloca_ids cs after`, `ss`]
    mp_tac abi_native_array_parent_allocation >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_native_array_parent_cursor >> DISCH_TAC >>
  qspecl_then [`cs`, `dst_addr`, `root_addr`, `ss`] strip_assume_tac abi_native_array_parent_context >>
  qspecl_then [`func`, `cs`, `after`, `parent_inst`, `abi_static_loop_counter_addr cs.cs_next_id ss`,
    `abi_dynarray_entry_cut dst src cs`, `abi_dynarray_entry_boundary cs dst_addr root_addr ss`, `dst_addr`, `payload`,
    `ss`, `abi_dynarray_entry_boundary cs dst_addr root_addr ss`] mp_tac abi_native_array_parent_frame >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `cs`, `dst`, `src`, `dst_addr`, `root_addr`, `ss`]
    mp_tac abi_native_array_parent_path >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `compiler_id_history (abi_dynarray_entry_cut dst src cs)` by (drule_all abi_native_array_parent_history >> simp[]) >>
  `cs_extends cs (abi_dynarray_entry_cut dst src cs) /\
    cs.cs_next_var <= (abi_dynarray_entry_cut dst src cs).cs_next_var` by
    simp[abi_dynarray_cuts_extend, abi_dynarray_entry_cut_def] >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==>
    eval_operand arg_op (abi_dynarray_entry_boundary cs dst_addr root_addr ss) = eval_operand arg_op ss` by
    (rpt strip_tac >> drule_all abi_native_array_parent_old_operand >> simp[]) >>
  conj_tac >- (PURE_REWRITE_TAC [abi_native_traversal_def] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native array parent execution readiness: " ^ name)
  end) (DB.thms "abiNativeArrayParentReady")
