(* TOP-LEVEL: actual word stores and full-layout memory copies execute in
   their containing function, including zero-sized copies and replayed SSA
   names. Helpers expose their exact code and state effects. *)
Theory memoryStoreCode
Ancestors
  typedCopyStateFrame context compileEnv exprLoweringProps emitHelper emitHelperProps
  fragBlockPath fragExec instIdxIndep ssaOperandFrame
  venomState venomExecSemantics venomInst list rich_list words

Definition memory_copy_result_def:
  memory_copy_result copy_size (dst:bytes32) (src:bytes32) ss =
    if copy_size = 0 then ss else mcopy (w2n dst) (w2n src) copy_size ss
End

Theorem memory_copy_result_state_frame[simp]:
  !copy_size dst src before after.
    copy_state_frame before (memory_copy_result copy_size dst src after) <=>
    copy_state_frame before after
Proof
  rpt gen_tac >> simp[memory_copy_result_def] >> rw[]
QED

Theorem compile_copy_memory_code:
  !dst src copy_size cs ret cs'.
    compile_copy_memory dst src copy_size cs = (ret,cs') ==>
    ret = () /\ same_blocks cs cs' /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    emitted_insts cs cs' =
      if copy_size = 0 then []
      else [mk_inst cs.cs_next_id MCOPY [dst; src; Lit (n2w copy_size)] []]
Proof
  rpt gen_tac >> Cases_on `copy_size` >>
  simp[compile_copy_memory_def, comp_return_def, emit_void_def, comp_bind_def,
    fresh_id_def, emit_def, emitted_insts_def, same_blocks_def,
    DROP_APPEND1, DROP_LENGTH_NIL] >> rpt strip_tac >>
  gvs[DROP_APPEND1, DROP_LENGTH_NIL]
QED

Theorem compile_copy_memory_execution:
  !dst src copy_size cs ret cs' ss dst_addr src_addr.
    compile_copy_memory dst src copy_size cs = (ret,cs') /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    copy_size < dimword(:256) ==>
    run_inst_seq (emitted_insts cs cs') ss =
      OK (memory_copy_result copy_size dst_addr src_addr ss)
Proof
  rpt gen_tac >> strip_tac >> drule compile_copy_memory_code >> strip_tac >>
  Cases_on `copy_size = 0` >>
  simp[memory_copy_result_def, run_inst_seq_def, Once step_inst_base_def,
    mk_inst_def, eval_operand_lit]
QED

Theorem compile_copy_memory_path:
  !ctx func dst src copy_size cs ret cs' ss dst_addr src_addr.
    compile_copy_memory dst src copy_size cs = (ret,cs') /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    copy_size < dimword(:256) /\ fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    fragment_path ctx func ss
      ((memory_copy_result copy_size dst_addr src_addr ss)
        with vs_inst_idx := LENGTH cs'.cs_current_insts) /\
    (memory_copy_result copy_size dst_addr src_addr ss).vs_current_bb = cs'.cs_current_bb /\
    copy_state_frame ss ((memory_copy_result copy_size dst_addr src_addr ss)
      with vs_inst_idx := LENGTH cs'.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_copy_memory_execution >> strip_tac >>
  drule compile_copy_memory_code >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`,
    `memory_copy_result copy_size dst_addr src_addr ss`] fragment_path_emitted) >>
  simp[mk_inst_def, is_terminator_def] >> Cases_on `copy_size = 0` >> simp[mk_inst_def, is_terminator_def]
QED

Theorem compile_store_word_code:
  !cenv src dst dst_ty src_ty cs ret cs'.
    is_word_type dst_ty /\ compile_store_memory cenv src dst dst_ty src_ty cs = (ret,cs') ==>
    ret = () /\ same_blocks cs cs' /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    emitted_insts cs cs' = [mk_inst cs.cs_next_id MSTORE [dst; src] []]
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_store_memory_def, emit_void_def, comp_bind_def, fresh_id_def,
    emit_def, emitted_insts_def, same_blocks_def, DROP_APPEND1, DROP_LENGTH_NIL]
QED

Theorem compile_store_word_execution:
  !cenv src dst dst_ty src_ty cs ret cs' ss dst_addr src_word.
    is_word_type dst_ty /\ compile_store_memory cenv src dst dst_ty src_ty cs = (ret,cs') /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_word ==>
    run_inst_seq (emitted_insts cs cs') ss = OK (mstore (w2n dst_addr) src_word ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_store_word_code >> strip_tac >>
  `step_inst_base (mk_inst cs.cs_next_id MSTORE [dst; src] []) ss =
    OK (mstore (w2n dst_addr) src_word ss)` by (irule step_MSTORE >> simp[]) >>
  simp[run_inst_seq_def]
QED

Theorem compile_store_word_path:
  !ctx func cenv src dst dst_ty src_ty cs ret cs' ss dst_addr src_word.
    is_word_type dst_ty /\ compile_store_memory cenv src dst dst_ty src_ty cs = (ret,cs') /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_word /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    fragment_path ctx func ss
      ((mstore (w2n dst_addr) src_word ss) with vs_inst_idx := LENGTH cs'.cs_current_insts) /\
    (mstore (w2n dst_addr) src_word ss).vs_current_bb = cs'.cs_current_bb /\
    copy_state_frame ss ((mstore (w2n dst_addr) src_word ss)
      with vs_inst_idx := LENGTH cs'.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_store_word_execution >> strip_tac >>
  drule_all compile_store_word_code >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`,
    `mstore (w2n (dst_addr:bytes32)) src_word ss`] fragment_path_emitted) >>
  simp[mk_inst_def, is_terminator_def]
QED
