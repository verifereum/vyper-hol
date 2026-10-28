(* TOP-LEVEL: the actual final MLOAD returns the complete encoding length.
   Its allocation-free execution composes with the enclosing field trace
   to produce the native result for the whole parent compiler action. *)
Theory abiNativeComplexFinish
Ancestors
  abiNativeDynamicState abiNativeTraversal abiNativeTraversalStep abiNativeEncodingDefs
  abiMemoryFieldsState abiMemoryLeafRun abiFieldOperands abiFieldLayoutDefs abiComplexLength abiComplexStructure
  abiAllocatorState abiStateFrame abiStateFrameOps abiMemoryFrame abiAllocationWindows
  compileIdFlow compileEnv emitHelperProps abiStaticLoopCode memoryReadProps fragExec venomState list words arithmetic

Theorem abi_native_complex_length:
  !ctx func full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity source_offset head_offset cs ret after ss.
    abi_memory_fields_state full dst src dyn_ptr (abi_field_head_size full) dst_addr dyn_addr root_addr
      source_capacity [] source_offset head_offset cs ss /\
    emit_op MLOAD [dyn_ptr] cs = (ret,after) /\ fn_has_code cs after func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out. abi_native_encoding_result ctx func cs after ret dst_addr
      (abi_field_bytes (abi_field_head_size full) full) ss out /\ ~out.vs_halted
Proof
  rpt gen_tac >> strip_tac >> drule abi_memory_fields_state_complete >> strip_tac >>
  qpat_assum `abi_memory_fields_state _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_memory_fields_state_def]) >>
  qpat_assum `abi_memory_fields_operands _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_memory_fields_operands_def]) >>
  drule_all emit_abi_complex_length_path >> disch_then (qspec_then `ctx` (qx_choose_then `out` strip_assume_tac)) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `abi_state_frame ss out` by (drule_all abi_state_frame_var_image >> simp[]) >>
  `abi_allocator_state out = abi_allocator_state ss` by
    (qpat_assum `out with vs_vars := _ = _`
       (mp_tac o AP_TERM ``abi_allocator_state``) >> simp[]) >>
  `abi_memory_frame [(w2n dst_addr,LENGTH (abi_field_bytes (abi_field_head_size full) full))] ss out` by
    (irule abi_memory_frame_memory >> first_assum MATCH_ACCEPT_TAC) >>
  `read_memory (w2n dst_addr) (LENGTH (abi_field_bytes (abi_field_head_size full) full)) out =
    abi_field_bytes (abi_field_head_size full) full` by fs[read_memory_def] >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss` by
    (rpt gen_tac >> DISCH_TAC >>
     qpat_assum `!arg_op. arg_op <> ret ==> _` (qspec_then `arg_op` mp_tac) >>
     `arg_op <> ret` by
       (qpat_x_assum `abi_operand_before _ _` (mp_tac o PURE_REWRITE_RULE [abi_operand_before_def]) >>
        disch_then (qspec_then `cs.cs_next_var` mp_tac) >> simp[compiler_var_name_def]) >> simp[]) >>
  `abi_encoding_result ctx func cs after ret dst_addr (abi_field_bytes (abi_field_head_size full) full) [] ss out` by
    (PURE_REWRITE_TAC [abi_encoding_result_def] >> asm_simp_tac bool_ss []) >>
  drule_all abi_native_encoding_allocation_free >> DISCH_TAC >> qexists_tac `out` >> gvs[]
QED

Theorem abi_native_complex_finish:
  !ctx func root_cs after dst_addr full initial cs ss dst src dyn_ptr dyn_addr root_addr source_capacity
      reference source_offset head_offset ret.
    abi_native_traversal ctx func root_cs after dst_addr (abi_field_bytes (abi_field_head_size full) full) initial cs ss /\
    alloca_inv initial /\
    abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
      [] source_offset head_offset cs ss /\
    emit_op MLOAD [dyn_ptr] cs = (ret,after) /\ fn_has_code cs after func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out. abi_native_encoding_result ctx func root_cs after ret dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial out
Proof
  rpt gen_tac >> strip_tac >> drule abi_native_dynamic_memory_state >> DISCH_TAC >>
  drule_all abi_native_complex_length >> disch_then (qspec_then `ctx` (qx_choose_then `out` strip_assume_tac)) >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  `cs_extends cs after` by (drule_all abi_complex_length_extends >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `compiler_id_history after` by
    (qspecl_then [`emit_op MLOAD [dyn_ptr]`, `cs`, `ret`, `after`] mp_tac compiler_id_flow_result >>
     impl_tac >- simp[compiler_id_flow_emit_helpers] >> strip_tac >>
     first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`ctx`, `func`, `root_cs`, `after`, `dst_addr`, `abi_field_bytes (abi_field_head_size full) full`,
    `initial`, `cs`, `after`, `ret`, `dst_addr`, `abi_field_bytes (abi_field_head_size full) full`, `ss`, `out`]
    mp_tac abi_native_traversal_native_step >> impl_tac >- asm_simp_tac (srw_ss()) [cs_extends_refl] >> DISCH_TAC >>
  qpat_x_assum `abi_native_traversal _ _ _ _ _ _ _ _ out`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  qpat_x_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def, abi_encoding_result_def]) >>
  qexists_tac `out` >> PURE_REWRITE_TAC [abi_native_encoding_result_def, abi_encoding_result_def] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual mixed complex final load and result: " ^ name)
  end) (DB.thms "abiNativeComplexFinish")
