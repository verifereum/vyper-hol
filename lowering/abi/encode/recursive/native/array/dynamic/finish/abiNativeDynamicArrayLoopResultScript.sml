(* TOP-LEVEL: execute the actual dynamic-array macro from its entry,
   including both allocation requests, semantic recursive children and
   the final exit. The result records the complete array bytes and trace. *)
Theory abiNativeDynamicArrayLoopResult
Ancestors
  abiNativeDynamicArrayHeaderResult abiNativeDynamicArrayStartInvariant abiNativeDynamicArrayStartTraversal
  abiNativeDynamicArrayStartState abiNativeDynamicArrayStartCode abiNativeDynamicArrayFlow abiNativeArrayBodyReady
  abiNativeTraversal abiNativeTraversalStep abiNativeTraversalResult abiNativeEncodingDefs abiNativeFields abiMemoryLeafRun
  abiDynamicLoopCode abiFieldOperands abiFieldLayoutDefs abiStaticLoopCode abiNativeDynamicArrayInvariant
  compileAllocaProvenance compileEnv fragExec venomMemDefs venomState venomInst list words arithmetic

Theorem abi_native_dynamic_array_loop_result:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride ss reference
      dst src len_op ret child_len mid.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) ss /\
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\ fn_has_code cs after func /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\ eval_operand len_op ss = SOME (n2w (LENGTH fields)) /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\ abi_operand_before cs.cs_next_var len_op /\
    32 <= source_capacity /\ LENGTH fields < dimword (:256) /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) (source_capacity - 32) ss.vs_memory fields /\
    mload (w2n root_addr) ss = n2w (LENGTH fields) /\ mload (w2n dst_addr) ss = n2w (LENGTH fields) /\
    abi_native_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) reference fields /\
    mem_bytes_at (w2n root_addr) source_capacity reference = mem_bytes_at (w2n root_addr) source_capacity ss.vs_memory ==>
    ?out. abi_native_encoding_result ctx func cs after ret dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) ss out
Proof
  rpt gen_tac >> strip_tac >> `alloca_inv ss /\ compiler_id_history cs` by fs[abi_native_memory_ready_def] >>
  drule_all abi_native_array_body_ready >> strip_tac >>
  drule_all abi_native_dynamic_array_start_invariant >> disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `mem_bytes_at (w2n root_addr) source_capacity reference = mem_bytes_at (w2n root_addr) source_capacity
    (abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss).vs_memory` by asm_simp_tac bool_ss [] >>
  `abi_operand_before (cs.cs_next_var + 3) dst /\ abi_operand_before (cs.cs_next_var + 3) src /\
    abi_operand_before (cs.cs_next_var + 3) len_op` by
    (rpt conj_tac >> irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> simp[]) >>
  `(abi_native_dynamic_array_tail_inst cs).inst_id <> (abi_native_dynamic_array_index_inst cs).inst_id` by
    simp[abi_native_dynamic_array_tail_inst_def, abi_native_dynamic_array_index_inst_def, mk_inst_def] >>
  drule_all abi_native_dynamic_array_header_result >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `ss`]
    mp_tac abi_native_traversal_initial >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `ss`, `ss`,
    `dst`, `src`, `info`, `width`, `stride`, `len_op`, `cs`, `ret`, `after`, `child_len`, `mid`, `n2w (LENGTH fields)`]
    mp_tac abi_native_dynamic_array_start_traversal >> impl_tac >- simp[cs_extends_refl] >> strip_tac >>
  drule_all abi_native_dynamic_array_flow >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `ss`, `cs`, `after`, `ret`,
    `dst_addr`, `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`,
    `abi_native_dynamic_array_start_state cs width (n2w (LENGTH fields)) ss`, `out`]
    mp_tac abi_native_traversal_native_step >> impl_tac >- simp[cs_extends_refl] >> DISCH_TAC >>
  qpat_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def, abi_encoding_result_def]) >>
  qexists_tac `out` >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `ss`, `after`, `out`, `ret`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`]
    mp_tac abi_native_traversal_result >> impl_tac >- simp[] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete actual dynamic array macro native result: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayLoopResult")
