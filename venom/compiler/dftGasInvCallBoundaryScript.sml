Theory dftGasInvCallBoundary
Ancestors
  dftGasOracleDefs venomExecSemantics

Theorem ev_step_invoke_OK:
  call_inst.inst_opcode = INVOKE /\
  ev_step orc p d fuel ctx call_inst s = OK s' ==>
  ?nm ops callee args cs ret cs'.
    decode_invoke call_inst = SOME (nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\
    setup_callee callee args s = SOME cs /\
    ev_blocks orc ((d,call_inst.inst_id)::p) d fuel ctx callee cs = IntRet ret cs' /\
    bind_outputs call_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s cs')) = SOME s'
Proof
  rpt strip_tac >>
  gvs[Once ev_step_def, AllCaseEqs()]
QED

Theorem ev_step_non_invoke_local:
  !orc p d fuel fuel' ctx ctx' inst s.
    inst.inst_opcode <> INVOKE ==>
    ev_step orc p d fuel ctx inst s =
    ev_step orc p d fuel' ctx' inst s
Proof
  rpt strip_tac >> simp[ev_step_def]
QED
