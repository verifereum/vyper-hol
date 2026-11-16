(* The output allocation is a single actual run, including ALLOCA 0. *)
Theory bodyFullRawCallOutbuf
Ancestors
  bodyFullAllocaFresh bodyFullGhostFrame bodyFullUnwrapRun
  immutableRegionLoadPtr bodyFullAllocGeneric
  builtinSystem context emitHelper emitHelperProps
  exprSimAlloc allocationPtr exprLoweringProps loweringHalt
  bodyPtrDefs loweringStateRelDefs compileEnv ptrDiscipline
  fragGasSeqPtr fragExecMem ptrSafetyTransport venomMemDefs
  venomState venomInst venomExecSemantics finite_map words list rich_list

Theorem outbuf_parts[local]:
  compile_raw_call_outbuf M sa = ((ov,op),sb) ==>
  ?buf sm.
    compile_alloc_buffer (if M = 0 then 0 else ((M+31) DIV 32)*32+32) sa = (buf,sm) /\
    ov = buf.buf_operand /\
    (if M = 0 then op = ov /\ sb = sm
     else emit_op ADD [ov;Lit 32w] sm = (op,sb))
Proof
  Cases_on `M = 0` >>
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]
QED
