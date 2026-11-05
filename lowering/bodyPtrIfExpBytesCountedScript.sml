Theory bodyPtrIfExpBytesCounted
Ancestors
  bodyPtrIfExpCopyHeader bodyPtrIfExpCopyInputs typedCopyPtr fragGasSeqPtr
  context compileEnv emitHelper exprLoweringProps rich_list venomInst

Theorem compile_store_bytestring_stages:
  !src dst sa sb.
    compile_store_bytestring src dst sa = ((),sb) ==>
    ?s1 s2 s3 s4 r1 r2 r3 r4.
      emit_op MLOAD [src] sa = (r1,s1) /\
      emit_op ADD [r1; Lit 31w] s1 = (r2,s2) /\
      emit_op AND [r2; Lit (i2w (-32))] s2 = (r3,s3) /\
      emit_op ADD [r3; Lit 32w] s3 = (r4,s4) /\
      emit_void MCOPY [dst;src;r4] s4 = ((),sb)
Proof
  rpt gen_tac >>
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
       comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem compile_store_bytestring_code:
  !src dst sa sb.
    compile_store_bytestring src dst sa = ((),sb) ==>
    EVERY (\i. i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
      (emitted_insts sa sb)
Proof
  rpt strip_tac >>
  gvs[compile_store_bytestring_def, compile_bytestring_copy_len_def,
      emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      emitted_insts_def, DROP_APPEND1] >>
  simp[mk_inst_def, is_terminator_def]
QED
