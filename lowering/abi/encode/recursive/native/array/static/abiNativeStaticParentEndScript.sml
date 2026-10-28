(* TOP-LEVEL: a completed generated static loop retains its parent cursor,
   parent word and parent operand. The real loop result precedes the final
   SSA frontier and can safely be consumed by the parent epilogue. *)
Theory abiNativeStaticParentEnd
Ancestors
  abiNativeStaticHeaderCode abiStaticLoopExec abiStaticLoopCode abiNativeArrayReadFrame abiNativeArrayBudget
  abiNativeTraversal abiNativeCursor abiNativeEncodingDefs abiMemoryLeafRun abiFieldOperands abiMemoryFrame
  abiAllocatedWindows allocationPathGrowth compileIdFlow compileAllocaProvenance compileEnv fragExec
  venomMemDefs venomState list words arithmetic

Theorem abi_native_static_loop_result_before:
  !dst src info width stride len_op cs ret after.
    compile_abi_encode_dyn_static_loop dst src info width stride len_op cs = (ret,after) ==>
    abi_operand_before after.cs_next_var ret
Proof
  rpt gen_tac >> strip_tac >> drule compile_abi_encode_dyn_static_loop_cut >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_operand_before_def, compiler_var_name_def] >> rpt strip_tac >> decide_tac
QED

Theorem abi_native_static_parent_end:
  !ctx func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload initial
      parent_inst parent_addr counter_inst counter_addr parent_ptr dst src info width stride len_op cs ret after ss out scratch.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr payload initial (abi_native_static_header_cut cs) ss /\
    abi_native_cursor func root_cs root_after parent_inst parent_addr (abi_native_static_header_cut cs) ss /\
    abi_native_cursor func root_cs root_after counter_inst counter_addr (abi_native_static_header_cut cs) ss /\
    parent_inst.inst_id <> counter_inst.inst_id /\
    compile_abi_encode_dyn_static_loop dst src info width stride len_op cs = (ret,after) /\
    abi_encoding_result ctx func (abi_native_static_header_cut cs) after ret dst_addr payload scratch ss out /\
    abi_memory_frame [(w2n dst_addr,LENGTH payload);(w2n counter_addr,32)] ss out /\
    abi_operand_before (abi_native_static_header_cut cs).cs_next_var parent_ptr ==>
    abi_native_cursor func root_cs root_after parent_inst parent_addr after out /\
    mload (w2n parent_addr) out = mload (w2n parent_addr) ss /\
    eval_operand parent_ptr out = eval_operand parent_ptr ss /\
    abi_operand_before after.cs_next_var parent_ptr /\ abi_operand_before after.cs_next_var ret
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_traversal_root_ready >> DISCH_TAC >>
  qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ ss`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
  qspecl_then [`func`, `root_cs`, `root_after`, `parent_inst`, `parent_addr`, `abi_native_static_header_cut cs`,
    `ss`, `source_id`, `target_id`] mp_tac abi_native_cursor_root_distinct >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_native_cursor _ _ _ parent_inst _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  qpat_assum `abi_native_cursor _ _ _ counter_inst _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  qspecl_then [`ss`, `out`, `parent_inst.inst_id`, `target_id`, `counter_inst.inst_id`, `parent_addr`,
    `dst_addr`, `payload`, `counter_addr`] mp_tac abi_native_array_counter_preserved >>
  impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qpat_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  `allocation_growth ss out` by (drule_all fragment_path_allocation_growth >> simp[]) >>
  `cs_extends (abi_native_static_header_cut cs) after` by
    (drule_all abi_native_static_header_continuation >> simp[]) >>
  `abi_native_cursor func root_cs root_after parent_inst parent_addr after out` by
    (qspecl_then [`func`, `root_cs`, `root_after`, `parent_inst`, `parent_addr`, `abi_native_static_header_cut cs`,
       `ss`, `after`, `out`] mp_tac abi_native_cursor_step >> impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []) >>
  `eval_operand parent_ptr out = eval_operand parent_ptr ss` by
    (first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  `abi_operand_before after.cs_next_var parent_ptr` by
    (qspecl_then [`(abi_native_static_header_cut cs).cs_next_var`, `after.cs_next_var`, `parent_ptr`]
       mp_tac abi_operand_before_mono >> impl_tac
     >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >> drule compile_abi_encode_dyn_static_loop_cut >> strip_tac >>
         asm_simp_tac (srw_ss()) [abi_native_static_header_cut_def] >> decide_tac) >> simp_tac bool_ss []) >>
  `abi_operand_before after.cs_next_var ret` by (drule_all abi_native_static_loop_result_before >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual static loop parent preservation: " ^ name)
  end) (DB.thms "abiNativeStaticParentEnd")
