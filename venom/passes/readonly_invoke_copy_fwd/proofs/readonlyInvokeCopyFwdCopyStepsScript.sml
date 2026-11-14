(* Eliminated copies are operationally distinct from ordinary instructions:
   only the current cross set grows, not the inherited relocation maps. *)
Theory readonlyInvokeCopyFwdCopySteps
Ancestors
  readonlyInvokeCopyFwdMemory readonlyInvokeCopyFwdRel
  venomExecSemantics venomState taintAgree ptrDiscipline
  finite_map words list pred_set

Theorem ricf_cert_forwarded_copy_step:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  inst.inst_opcode = MCOPY /\
  inst.inst_operands = [op_dst; op_src; op_size] /\
  inst.inst_outputs = [] /\ nop.inst_opcode = NOP /\
  nop.inst_operands = [] /\ nop.inst_outputs = [] /\
  eval_operand op_dst s = SOME dst /\
  eval_operand op_src s = SOME src /\
  eval_operand op_size s = SOME sz /\
  db = w2n dst /\ sb = w2n src /\ len = w2n sz /\
  db+len <= dimword (:256) /\ sb+len <= dimword (:256) /\
  {i | db <= i /\ i < db+len} SUBSET ircf_dead ids s stk /\
  (!j i. j < LENGTH stk /\ db <= i /\ i < db+len /\
    i < (EL j stk).cf_state.vs_alloca_next ==>
    i IN ircf_dead ids (EL j stk).cf_state (DROP (SUC j) stk)) /\
  (db+len <= sb \/ sb+len <= db) /\
  (!q. q < len /\ sb+q NOTIN tn0.t_mem ==>
    read_byte (sb+q) s.vs_memory = read_byte (sb+q) t.vs_memory) /\
  un = tn0 with t_mem :=
    (tn0.t_mem DIFF {i | db <= i /\ i < db+len}) UNION
    {db+q | q < len /\ sb+q IN tn0.t_mem} /\
  (!gam. gam = cur \/ MEM gam curs \/ gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !b c z k. (b,c,z) IN gam /\ k < z ==>
      ~(db <= b+k /\ b+k < db+len) /\
      ~(db <= c+k /\ c+k < db+len)) ==>
  step_inst_base inst s = OK (mcopy db sb len s) /\
  step_inst_base nop t = OK t /\
  ricf_cert_core D ids stk PG G
    (if s.vs_prev_bb = NONE then un else entry_taint_vars fn s un)
    fn sites maps targets G0 un (cur UNION {(db,sb,len)}) curs
    (mcopy db sb len s) t
Proof
  strip_tac >>
  `ricf_cert_core D ids stk PG G
     (if s.vs_prev_bb = NONE then un else entry_taint_vars fn s un)
     fn sites maps targets G0 un (cur UNION {(db,sb,len)}) curs
     (mcopy db sb len s) t` by
    (irule ricf_cert_activate_copy >> metis_tac[]) >>
  simp[step_inst_base_opcode_eqs]
QED
