Theory dftGasFromListTraceSuccessor
Ancestors
  dftGasFromListTraceLift dftGasFromListTraceExtend dftGasFromListLookup
  dftGasFromListOpenTrace dftGasFromListTraceDefs venomInstProofs
  venomExecProofs venomExecSemantics venomWf contextCodegenRel
  venomInst venomState list arithmetic

Theorem trace_context_next:
  MEM ((p,d,inst.inst_id),fn,inst,t) (trace_context n ctx s0) /\
  wf_function fn /\ active_inst fn inst t /\
  ~is_terminator inst.inst_opcode /\ step_inst f ctx inst t = OK u /\
  active_inst fn j (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  !b. ?m. b <= m /\
    MEM ((p,d,j.inst_id),fn,j,u with vs_inst_idx := SUC t.vs_inst_idx)
      (trace_context m ctx s0)
Proof
  strip_tac >> drule trace_context_cofinal >> strip_tac >>
  `u.vs_current_bb = t.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  drule_all wf_active_lookup >> strip_tac >> gvs[] >>
  `MEM ((p,d,j.inst_id),fn,j,u with vs_inst_idx := SUC t.vs_inst_idx)
    (open_trace p d f ctx fn bb t)` by
    (drule_all open_trace_next >>
     disch_then (qspecl_then [`p`,`fn`,`d`] SUBST1_TAC) >>
     `MEM ((p,d,j.inst_id),fn,j,u with vs_inst_idx := SUC t.vs_inst_idx)
       (trace_block p d f ctx fn bb (u with vs_inst_idx := SUC t.vs_inst_idx))` by
       simp[Once trace_defs] >>
     simp[open_trace_def]) >>
  gen_tac >> qpat_x_assum `!k b. _` (qspecl_then [`f`,`b`] strip_assume_tac) >>
  qexists_tac `m` >> simp[]
QED

Theorem trace_context_block:
  MEM ((p,d,inst.inst_id),fn,inst,t) (trace_context n ctx s0) /\
  wf_function fn /\ is_terminator inst.inst_opcode /\
  step_inst f ctx inst t = OK u /\ ~u.vs_halted /\
  enters_block fn u z /\ active_inst fn j z ==>
  !b. ?m. b <= m /\
    MEM ((p,SUC d,j.inst_id),fn,j,z) (trace_context m ctx s0)
Proof
  strip_tac >> drule trace_context_cofinal >> strip_tac >>
  `MEM ((p,SUC d,j.inst_id),fn,j,z)
    (trace_blocks p d (SUC f) ctx fn u)` by
    (irule trace_entered_head >> simp[]) >>
  `step_inst (SUC f) ctx inst t = OK u` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `f` >> simp[]) >>
  `exec_block (SUC f) ctx bb t = OK u` by
    simp[Once exec_block_def] >>
  `MEM ((p,SUC d,j.inst_id),fn,j,z)
    (open_trace p d (SUC f) ctx fn bb t)` by simp[open_trace_def] >>
  gen_tac >> qpat_x_assum `!k b. _`
    (qspecl_then [`SUC f`,`b`] strip_assume_tac) >>
  qexists_tac `m` >> simp[]
QED

Theorem trace_context_callee:
  MEM ((p,d,inst.inst_id),fn,inst,t) (trace_context n ctx s0) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\ wf_function callee /\
  eval_operands ops t = SOME args /\ setup_callee callee args t = SOME cs /\
  enters_block callee cs z /\ active_inst callee j z ==>
  !b. ?m. b <= m /\
    MEM ((((d,inst.inst_id)::p),SUC d,j.inst_id),callee,j,z)
      (trace_context m ctx s0)
Proof
  strip_tac >> drule trace_context_cofinal >> strip_tac >>
  `MEM ((((d,inst.inst_id)::p),SUC d,j.inst_id),callee,j,z)
    (trace_blocks ((d,inst.inst_id)::p) d 1 ctx callee cs)` by
    (irule (SRULE [] (Q.INST [`fuel` |-> `0`] trace_entered_head)) >> simp[]) >>
  `MEM ((((d,inst.inst_id)::p),SUC d,j.inst_id),callee,j,z)
    (trace_step p d 1 ctx fn inst t)` by simp[Once trace_defs] >>
  `MEM ((((d,inst.inst_id)::p),SUC d,j.inst_id),callee,j,z)
    (open_trace p d 1 ctx fn bb t)` by
    (simp[open_trace_def] >> disj1_tac >> simp[Once trace_defs]) >>
  gen_tac >> qpat_x_assum `!k b. _`
    (qspecl_then [`1`,`b`] strip_assume_tac) >>
  qexists_tac `m` >> simp[]
QED
