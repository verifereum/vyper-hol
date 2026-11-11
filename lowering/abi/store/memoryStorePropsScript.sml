(* TOP-LEVEL: actual word and bulk stores establish complete typed values,
   preserve disjoint typed regions and leave operand values intact.
   Helpers cover zero-sized layouts without executing a spurious MCOPY. *)
Theory memoryStoreProps
Ancestors
  valueEncodingDefs typedCopyStateFrame memoryStoreCode memoryValueDefs memoryValueTyping memoryValueFrame memoryValueRelocation
  memoryReadProps valueLoadProps valueEncoding valueEncodingProps
  context compileEnv fragBlockPath fragExec instIdxIndep ssaOperandFrame dynCopyExec
  vyperTyping vyperValue venomState list words arithmetic

Theorem memory_copy_result_layout:
  !tv v copy_size dst_addr src_addr ss.
    memory_value_rel tv v (w2n src_addr) ss.vs_memory /\ val_wf tv v /\
    type_memory_size tv <= copy_size ==>
    memory_value_rel tv v (w2n dst_addr)
      (memory_copy_result copy_size dst_addr src_addr ss).vs_memory
Proof
  rpt gen_tac >> strip_tac >> Cases_on `copy_size = 0` >> simp[memory_copy_result_def]
  >- (`type_memory_size tv = 0` by decide_tac >>
      mp_tac (Q.SPECL [`tv`, `v`, `w2n (src_addr:bytes32)`, `ss.vs_memory`,
        `w2n (dst_addr:bytes32)`, `ss.vs_memory`] memory_value_rel_relocate) >>
      simp[mem_bytes_at_def]) >>
  irule mcopy_establishes_memory_value_rel >> simp[]
QED

Theorem memory_copy_result_frame:
  !tv v offset copy_size dst_addr src_addr ss.
    memory_value_rel tv v offset ss.vs_memory /\ val_wf tv v /\
    (offset + type_memory_size tv <= w2n dst_addr \/ w2n dst_addr + copy_size <= offset) ==>
    memory_value_rel tv v offset
      (memory_copy_result copy_size dst_addr src_addr ss).vs_memory
Proof
  rpt gen_tac >> strip_tac >> Cases_on `copy_size = 0` >> simp[memory_copy_result_def] >>
  irule mcopy_preserves_memory_value_rel >> simp[]
QED

Theorem memory_copy_result_control[simp]:
  !copy_size dst_addr src_addr ss.
    (memory_copy_result copy_size dst_addr src_addr ss).vs_current_bb = ss.vs_current_bb /\
    (memory_copy_result copy_size dst_addr src_addr ss).vs_inst_idx = ss.vs_inst_idx /\
    (memory_copy_result copy_size dst_addr src_addr ss).vs_halted = ss.vs_halted /\
    (!arg_op. eval_operand arg_op (memory_copy_result copy_size dst_addr src_addr ss) =
      eval_operand arg_op ss)
Proof
  rpt gen_tac >> Cases_on `copy_size = 0` >>
  simp[memory_copy_result_def, eval_operand_mcopy_eq]
QED

Theorem compile_store_memory_bulk_path:
  !ctx func cenv dst_ty src_ty tv v dst src cs ret cs' ss dst_addr src_addr.
    ~is_word_type dst_ty /\ ~is_bytestring_type dst_ty /\
    (dst_ty = src_ty \/ tuple_memory_layout_eq dst_ty src_ty) /\
    compile_store_memory cenv src dst dst_ty src_ty cs = (ret,cs') /\
    memory_value_rel tv v (w2n src_addr) ss.vs_memory /\ val_wf tv v /\
    type_memory_size tv <= type_memory_bytes cenv dst_ty /\
    type_memory_bytes cenv dst_ty < dimword(:256) /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ copy_state_frame ss out /\ memory_value_rel tv v (w2n dst_addr) out.vs_memory /\
      (!arg_op. eval_operand arg_op out = eval_operand arg_op ss) /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_addr \/
          w2n dst_addr + type_memory_bytes cenv dst_ty <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `compile_copy_memory dst src (type_memory_bytes cenv dst_ty) cs = (ret,cs')` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [compile_store_memory_def] >>
     Cases_on `dst_ty = src_ty` >> fs[]) >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) compile_copy_memory_path >>
  `memory_value_rel tv v (w2n dst_addr)
    (memory_copy_result (type_memory_bytes cenv dst_ty) dst_addr src_addr ss).vs_memory` by
    (irule memory_copy_result_layout >> simp[]) >>
  qexists_tac `(memory_copy_result (type_memory_bytes cenv dst_ty) dst_addr src_addr ss)
    with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  simp[eval_op_inst_idx] >> rpt gen_tac >> DISCH_TAC >>
  irule memory_copy_result_frame >> simp[]
QED

Theorem compile_store_memory_word_value_path:
  !tenv ctx func cenv ty tv v dst src src_ty cs ret cs' ss dst_addr src_word.
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    compile_store_memory cenv src dst ty src_ty cs = (ret,cs') /\
    lowered_value_rel ty tv v src ss /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_word /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ copy_state_frame ss out /\ value_has_type tv v /\
      memory_value_rel tv v (w2n dst_addr) out.vs_memory /\
      (!arg_op. eval_operand arg_op out = eval_operand arg_op ss) /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_addr \/ w2n dst_addr + 32 <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) compile_store_word_path >>
  `memory_value_rel tv v (w2n dst_addr) (mstore (w2n dst_addr) src_word ss).vs_memory` by
    (mp_tac (Q.SPECL [`tenv`, `ty`, `tv`, `v`, `src`, `src_word`, `w2n (dst_addr:bytes32)`, `ss`]
      store_lowered_word_memory_value_rel) >> simp[]) >>
  qexists_tac `(mstore (w2n dst_addr) src_word ss) with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  simp[eval_op_inst_idx, eval_operand_mstore_eq] >> conj_tac
  >- fs[lowered_value_rel_def] >>
  rpt gen_tac >> DISCH_TAC >> irule mstore_preserves_memory_value_rel >> simp[]
QED
