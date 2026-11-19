Theory rawCallOutbufCompile
Ancestors
  builtinSystem context compileEnv emitHelper venomInst words
Libs
  pairLib

Theorem calldata_outbuf_compile:
  !n sa valop ptrop sb.
    compile_raw_call_outbuf n sa = ((valop,ptrop),sb) ==>
    ?buf sm. compile_alloc_buffer
      (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) sa = (buf,sm) /\
      valop = buf.buf_operand /\
      (if n = 0 then ptrop = valop /\ sb = sm
       else emit_op ADD [valop; Lit 32w] sm = (ptrop,sb))
Proof
  rpt gen_tac >> Cases_on `n = 0` >>
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED
