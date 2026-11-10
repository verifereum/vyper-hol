(* Executable meaningful-prefix stores for constructor immutables. *)
Theory immutableDeployAssignExecution
Ancestors
  immutableDeployAssignTransfer immutableDeployAssignWord
  immutableDeployAssignRanges exprSimCopy emitHelperProps
  context compileEnv venomInst exprLoweringProps immutableCopyExecution
  placeTypedCopyPath fragExec venomState stmtLowering valueEncoding

Theorem immutable_store_one_insts[local]:
  immutable_store_one imm src dst off sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb)
Proof
  simp[immutable_store_one_def, immutable_comp_bind_cases] >> strip_tac >>
  imp_res_tac code_offset_insts >>
  imp_res_tac immutable_byte_offset_extends >>
  drule emitted_insts_emit_op >> strip_tac >>
  `?tail. sb.cs_current_insts = st1''.cs_current_insts ++ tail /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) tail` by
    (qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `imm` >>
     simp[compile_imm_store_word_def, emitHelperTheory.emit_op_def,
          emitHelperTheory.emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[] >> simp[mk_inst_def]) >>
  pure_once_rewrite_tac[emitted_insts_def] >>
  qpat_x_assum `sb.cs_current_insts = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `st1''.cs_current_insts = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `st1'.cs_current_insts = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `st1.cs_current_insts = _` (fn th => pure_rewrite_tac[th]) >>
  simp[listTheory.DROP_APPEND, GSYM arithmeticTheory.SUB_RIGHT_SUB,
       mk_inst_def] >>
  fs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem immutable_store_words_insts:
  !n off sa sb.
  compile_imm_store_words imm src dst n off sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb)
Proof
  Induct
  >- (simp[compile_imm_store_words_def, comp_return_def] >>
      rpt strip_tac >> gvs[emitted_insts_def]) >>
  simp[immutable_store_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  rpt gen_tac >> strip_tac >>
  drule immutable_store_one_insts >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa st1 ++ emitted_insts st1 sb` by
    (irule emitted_insts_append >> simp[]) >>
  fs[listTheory.APPEND_ASSOC]
QED
