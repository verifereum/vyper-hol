Theory concretizePtrExternalCallContent
Ancestors concretizePtrBufferCopyContent venomCallOracleProps
  venomCallOracleDefs venomExecSemantics venomState codegenRel
  words list rich_list finite_map

Theorem ptr_exec_ext_call_content:
  inst.inst_outputs = [out] /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n at) (w2n az) t /\
  s.vs_call_ctx = t.vs_call_ctx /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  s.vs_logs = t.vs_logs /\
  s.vs_pending_deletions = t.vs_pending_deletions /\
  s.vs_outcomes = t.vs_outcomes /\ s.vs_requests = t.vs_requests ==>
  ?s' t'.
    exec_ext_call inst s gas addr value ao az ro rz st = OK s' /\
    exec_ext_call inst t gt addr value at az rt rz st = OK t' /\
    lookup_var out s' = lookup_var out t' /\
    s'.vs_returndata = t'.vs_returndata /\
    s'.vs_accounts = t'.vs_accounts /\ s'.vs_transient = t'.vs_transient /\
    s'.vs_logs = t'.vs_logs /\
    s'.vs_pending_deletions = t'.vs_pending_deletions /\
    s'.vs_outcomes = t'.vs_outcomes /\ s'.vs_requests = t'.vs_requests /\
    (!i. i < MIN (w2n rz) (LENGTH s'.vs_returndata) ==>
      read_byte (w2n ro+i) s'.vs_memory =
      read_byte (w2n rt+i) t'.vs_memory)
Proof
  strip_tac >>
  `venom_call_request s addr value ao az st =
   venom_call_request t addr value at az st` by
    (irule venom_call_request_agreement >> simp[]) >>
  simp[exec_ext_call_def, consume_call_outcome_eq,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule ptr_payload_write_content >> simp[LENGTH_TAKE_EQ]
QED

Theorem ptr_call_content:
  inst.inst_opcode = CALL /\
  inst.inst_operands = [gop;adop;vop;aop;azop;rop;rzop] /\
  inst.inst_outputs = [out] /\
  eval_operand gop s = SOME gas /\ eval_operand gop t = SOME gt /\
  eval_operand adop s = SOME addr /\ eval_operand adop t = SOME addr /\
  eval_operand vop s = SOME value /\ eval_operand vop t = SOME value /\
  eval_operand aop s = SOME ao /\ eval_operand aop t = SOME at /\
  eval_operand azop s = SOME az /\ eval_operand azop t = SOME az /\
  eval_operand rop s = SOME ro /\ eval_operand rop t = SOME rt /\
  eval_operand rzop s = SOME rz /\ eval_operand rzop t = SOME rz /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n at) (w2n az) t /\
  s.vs_call_ctx = t.vs_call_ctx /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  s.vs_logs = t.vs_logs /\
  s.vs_pending_deletions = t.vs_pending_deletions /\
  s.vs_outcomes = t.vs_outcomes /\ s.vs_requests = t.vs_requests /\
  ~(s.vs_call_ctx.cc_static /\ value <> 0w) ==>
  ?s' t'. step_inst_base inst s = OK s' /\ step_inst_base inst t = OK t' /\
    lookup_var out s' = lookup_var out t' /\
    s'.vs_returndata = t'.vs_returndata /\
    s'.vs_accounts = t'.vs_accounts /\ s'.vs_transient = t'.vs_transient /\
    s'.vs_logs = t'.vs_logs /\
    s'.vs_pending_deletions = t'.vs_pending_deletions /\
    s'.vs_outcomes = t'.vs_outcomes /\ s'.vs_requests = t'.vs_requests /\
    (!i. i < MIN (w2n rz) (LENGTH s'.vs_returndata) ==>
      read_byte (w2n ro+i) s'.vs_memory =
      read_byte (w2n rt+i) t'.vs_memory)
Proof
  strip_tac >>
  `s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static` by simp[] >>
  `~(t.vs_call_ctx.cc_static /\ value <> 0w)` by metis_tac[] >>
  asm_simp_tac (srw_ss()) [step_inst_base_def] >>
  irule (SIMP_RULE (srw_ss()) [] ptr_exec_ext_call_content) >> simp[]
QED

Theorem ptr_staticcall_content:
  inst.inst_opcode = STATICCALL /\
  inst.inst_operands = [gop;adop;aop;azop;rop;rzop] /\
  inst.inst_outputs = [out] /\
  eval_operand gop s = SOME gas /\ eval_operand gop t = SOME gt /\
  eval_operand adop s = SOME addr /\ eval_operand adop t = SOME addr /\
  eval_operand aop s = SOME ao /\ eval_operand aop t = SOME at /\
  eval_operand azop s = SOME az /\ eval_operand azop t = SOME az /\
  eval_operand rop s = SOME ro /\ eval_operand rop t = SOME rt /\
  eval_operand rzop s = SOME rz /\ eval_operand rzop t = SOME rz /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n at) (w2n az) t /\
  s.vs_call_ctx = t.vs_call_ctx /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
  s.vs_logs = t.vs_logs /\
  s.vs_pending_deletions = t.vs_pending_deletions /\
  s.vs_outcomes = t.vs_outcomes /\ s.vs_requests = t.vs_requests ==>
  ?s' t'. step_inst_base inst s = OK s' /\ step_inst_base inst t = OK t' /\
    lookup_var out s' = lookup_var out t' /\
    s'.vs_returndata = t'.vs_returndata /\
    s'.vs_accounts = t'.vs_accounts /\ s'.vs_transient = t'.vs_transient /\
    s'.vs_logs = t'.vs_logs /\
    s'.vs_pending_deletions = t'.vs_pending_deletions /\
    s'.vs_outcomes = t'.vs_outcomes /\ s'.vs_requests = t'.vs_requests /\
    (!i. i < MIN (w2n rz) (LENGTH s'.vs_returndata) ==>
      read_byte (w2n ro+i) s'.vs_memory =
      read_byte (w2n rt+i) t'.vs_memory)
Proof
  strip_tac >> asm_simp_tac (srw_ss()) [step_inst_base_def] >>
  irule (SIMP_RULE (srw_ss()) [] ptr_exec_ext_call_content) >> simp[]
QED

Theorem ptr_call_success_nonabort:
  inst.inst_opcode = CALL /\
  inst.inst_operands = [gop;adop;vop;aop;azop;rop;rzop] /\
  eval_operand gop t = SOME gas /\ eval_operand adop t = SOME addr /\
  eval_operand vop t = SOME value /\ eval_operand aop t = SOME ao /\
  eval_operand azop t = SOME az /\ eval_operand rop t = SOME ro /\
  eval_operand rzop t = SOME rz /\ step_inst_base inst t = OK t' ==>
  ~(t.vs_call_ctx.cc_static /\ value <> 0w)
Proof
  simp[step_inst_base_def] >> rpt strip_tac >> gvs[AllCaseEqs()]
QED
