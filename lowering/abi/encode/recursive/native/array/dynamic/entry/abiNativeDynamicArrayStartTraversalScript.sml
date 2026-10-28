(* TOP-LEVEL: actual setup writes only its two owned scratch cells and
   advances the enclosing traversal to the runtime header. The compiler
   context stays at the macro so the same profile covers all loop visits. *)
Theory abiNativeDynamicArrayStartTraversal
Ancestors
  abiNativeDynamicArrayStartCursors abiNativeDynamicArrayStartCode abiNativeDynamicArrayStartState abiNativeDynamicArrayParts
  abiNativeCursorWrites abiNativeCursor abiNativeTraversalLoop abiNativeTraversal abiNativeArrayBudget abiNativeEncodingDefs
  abiAllocationTrace abiAllocationWindows abiMemoryFrameCover abiMemoryFrame abiFieldOperands abiDynamicLoopCode abiStaticLoopEntry
  compileAllocaProvenance compileIdFlow compileEnv fragExec venomMemDefs venomState venomInst list pair words arithmetic

Theorem abi_native_dynamic_array_start_profile_frame:
  !func root_cs root_after cs width length_word ss dst src stride len_op.
    abi_native_cursor func root_cs root_after (abi_native_dynamic_array_index_inst cs)
      (abi_static_loop_counter_addr cs.cs_next_id ss) (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
      (abi_native_dynamic_array_start_state cs width length_word ss) /\
    abi_native_cursor func root_cs root_after (abi_native_dynamic_array_tail_inst cs)
      (abi_native_dynamic_array_tail_addr cs ss) (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
      (abi_native_dynamic_array_start_state cs width length_word ss) ==>
    abi_memory_frame (abi_allocation_windows (compiler_alloca_ids root_cs root_after)
      (abi_native_dynamic_array_start_state cs width length_word ss)) ss (abi_native_dynamic_array_start_state cs width length_word ss)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`func`, `root_cs`, `root_after`, `abi_dynamic_loop_prefix_cut dst src width stride len_op cs`,
    `abi_native_dynamic_array_start_state cs width length_word ss`,
    `[(abi_native_dynamic_array_index_inst cs,abi_static_loop_counter_addr cs.cs_next_id ss);
      (abi_native_dynamic_array_tail_inst cs,abi_native_dynamic_array_tail_addr cs ss)]`]
    mp_tac abi_native_cursor_writes_cover >> impl_tac >- simp[] >> simp_tac (srw_ss()) [MAP] >> DISCH_TAC >>
  irule abi_memory_frame_cover >>
  qexists_tac `[(w2n (abi_static_loop_counter_addr cs.cs_next_id ss),32);(w2n (abi_native_dynamic_array_tail_addr cs ss),32)]` >>
  simp[abi_native_dynamic_array_start_frame]
QED

Theorem abi_native_dynamic_array_start_traversal:
  !ctx func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload initial ss
      dst src info width stride len_op cs ret after child_len mid length_word.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr payload initial cs ss /\
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\
    fn_has_code cs after func /\ cs_extends after root_after /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand len_op ss = SOME length_word /\ abi_operand_before cs.cs_next_var len_op ==>
    abi_native_traversal ctx func root_cs root_after dst_addr payload initial cs (abi_native_dynamic_array_start_state cs width length_word ss) /\
    abi_native_cursor func root_cs root_after (abi_native_dynamic_array_index_inst cs)
      (abi_static_loop_counter_addr cs.cs_next_id ss) (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
      (abi_native_dynamic_array_start_state cs width length_word ss) /\
    abi_native_cursor func root_cs root_after (abi_native_dynamic_array_tail_inst cs)
      (abi_native_dynamic_array_tail_addr cs ss) (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
      (abi_native_dynamic_array_start_state cs width length_word ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_traversal_root_ready >> DISCH_TAC >>
  `alloca_inv initial` by fs[abi_native_memory_ready_def] >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  drule_all abi_native_dynamic_array_start_cursors >> disch_then (qspec_then `length_word` strip_assume_tac) >>
  drule_all abi_native_dynamic_array_start_profile_frame >> DISCH_TAC >>
  `MEM cs.cs_next_id (compiler_alloca_ids root_cs root_after) /\ MEM (cs.cs_next_id + 2) (compiler_alloca_ids root_cs root_after)` by
    fs[abi_native_cursor_def, abi_native_dynamic_array_index_inst_def, abi_native_dynamic_array_tail_inst_def, mk_inst_def] >>
  qspecl_then [`cs`, `width`, `length_word`, `compiler_alloca_ids root_cs root_after`, `ss`]
    mp_tac abi_native_dynamic_array_start_trace >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  drule_all abi_native_dynamic_array_parts >> strip_tac >>
  drule_all abi_native_dynamic_array_start_path >> disch_then (qspec_then `ctx` ASSUME_TAC) >>
  qspecl_then [`cs`, `width`, `length_word`, `ss`] strip_assume_tac abi_native_dynamic_array_start_frame >>
  `abi_memory_frame ((w2n dst_addr,LENGTH payload)::abi_allocation_windows (compiler_alloca_ids root_cs root_after)
    (abi_native_dynamic_array_start_state cs width length_word ss)) ss (abi_native_dynamic_array_start_state cs width length_word ss)` by
    (qspecl_then [`[(w2n dst_addr,LENGTH payload)]`,
       `abi_allocation_windows (compiler_alloca_ids root_cs root_after) (abi_native_dynamic_array_start_state cs width length_word ss)`,
       `ss`, `abi_native_dynamic_array_start_state cs width length_word ss`] mp_tac abi_memory_frame_append_right >> simp[]) >>
  `!arg_op. abi_operand_before root_cs.cs_next_var arg_op ==>
    eval_operand arg_op (abi_native_dynamic_array_start_state cs width length_word ss) = eval_operand arg_op ss` by
    (rpt gen_tac >> DISCH_TAC >> irule abi_native_dynamic_array_start_old_operand >>
     irule abi_operand_before_mono >> qexists_tac `root_cs.cs_next_var` >> simp[]) >>
  drule_all abi_native_traversal_runtime_step >> DISCH_TAC >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array setup enclosing traversal: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayStartTraversal")
