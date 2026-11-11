(* Code boundary for the concrete length prefix, shared by checked copies. *)
Theory logBytesCodePtr
Ancestors context compileEnv emitHelper exprLoweringProps venomInst list rich_list

Theorem compile_bytestring_copy_len_code:
  compile_bytestring_copy_len src sa = (out,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode = MLOAD \/ i.inst_opcode = ADD \/ i.inst_opcode = AND)
    (emitted_insts sa sb)
Proof
  strip_tac >>
  gvs[compile_bytestring_copy_len_def,emit_op_def,comp_bind_def,
    comp_ignore_bind_def,comp_return_def,fresh_id_def,fresh_var_def,emit_def,
    emitted_insts_def,DROP_APPEND1] >>
  simp[mk_inst_def,APPEND_ASSOC]
QED

Theorem compile_store_bytestring_opcodes:
  compile_store_bytestring src dst sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode = MLOAD \/ i.inst_opcode = ADD \/
    i.inst_opcode = AND \/ i.inst_opcode = MCOPY) (emitted_insts sa sb)
Proof
  strip_tac >>
  gvs[compile_store_bytestring_def,compile_bytestring_copy_len_def,
    emit_op_def,emit_void_def,comp_bind_def,comp_ignore_bind_def,
    comp_return_def,fresh_id_def,fresh_var_def,emit_def,
    emitted_insts_def,DROP_APPEND1] >>
  simp[mk_inst_def,APPEND_ASSOC]
QED
