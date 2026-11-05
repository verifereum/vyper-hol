Theory dftGasToListVisitEdge
Ancestors
  dftGasToListReachTrace dftGasToListReplay dftGasToListAgreement
  dftGasToListReachBoundary dftGasToListTrace dftGasOracleDefs
  contextCodegenRel venomInstProofs venomExecSemantics list

Inductive visit_edge:
[~next:]
  (!orc ctx p d fn inst t k u j.
    active_inst fn inst t /\ ~is_terminator inst.inst_opcode /\
    ev_step orc p d k ctx inst t = OK u /\
    active_inst fn j (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
    visit_edge orc ctx (TraceVisit p d fn inst t)
      (TraceVisit p d fn j (u with vs_inst_idx := SUC t.vs_inst_idx)) NONE)
[~jump:]
  (!orc ctx p d fn inst t k u z j.
    active_inst fn inst t /\ is_terminator inst.inst_opcode /\
    ev_step orc p d k ctx inst t = OK u /\ ~u.vs_halted /\
    enters_block fn u z /\ active_inst fn j z ==>
    visit_edge orc ctx (TraceVisit p d fn inst t)
      (TraceVisit p (SUC d) fn j z) (SOME (p,d,fn,u)))
[~callee:]
  (!orc ctx p d caller inv t nm ops callee args cs s1 inst.
    active_inst caller inv t /\ inv.inst_opcode = INVOKE /\
    decode_invoke inv = SOME (nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops t = SOME args /\ setup_callee callee args t = SOME cs /\
    enters_block callee cs s1 /\ active_inst callee inst s1 ==>
    visit_edge orc ctx (TraceVisit p d caller inv t)
      (TraceVisit ((d,inv.inst_id)::p) (SUC d) callee inst s1) NONE)
End

Theorem trace_visit_member:
  !ts a p d fn inst t.
    MEM (TraceVisit p d fn inst t) ts <=>
    ?n. MEM (n,p,d,fn,inst,t) (trace_visits a ts)
Proof
  Induct >> simp[trace_visits_def] >>
  Cases_on `h` >> simp[trace_visits_def] >> metis_tac[]
QED

Theorem visit_edge_jump_target:
  visit_edge orc ctx v w (SOME(p,d,fn,u)) ==>
  ~u.vs_halted /\ ?j z. w = TraceVisit p (SUC d) fn j z /\
    enters_block fn u z /\ active_inst fn j z
Proof
  simp[Once visit_edge_cases] >> metis_tac[]
QED

Theorem ev_step_nonterm_current_bb:
  ~is_terminator inst.inst_opcode /\ ev_step orc p d k ctx inst t = OK u ==>
  u.vs_current_bb = t.vs_current_bb
Proof
  rpt strip_tac >>
  qspec_then `trace_events (trace_step orc p d k ctx inst t)` assume_tac agrees_map >>
  drule (cj 1 trace_replay) >> simp[] >> strip_tac >>
  drule_all step_preserves_control_flow >> simp[]
QED

Theorem ev_next_instruction_lookup:
  ALL_DISTINCT (fn_labels fn) /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  ~is_terminator inst.inst_opcode /\ ev_step orc p d k ctx inst t = OK u /\
  active_inst fn j (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  get_instruction bb (SUC t.vs_inst_idx) = SOME j
Proof
  rpt strip_tac >> drule_all ev_step_nonterm_current_bb >> strip_tac >>
  drule_all active_inst_lookup_distinct >> simp[] >> strip_tac >> gvs[]
QED

Theorem visit_edge_jump_entry:
  ALL_DISTINCT (fn_labels fn) /\
  visit_edge orc ctx v w (SOME(p,d,fn,u)) ==>
  MEM w (trace_blocks orc p d (SUC fuel) ctx fn u)
Proof
  rpt strip_tac >> drule visit_edge_jump_target >> strip_tac >> gvs[] >>
  drule_all trace_blocks_entry_visit >> strip_tac >>
  metis_tac[trace_visit_member]
QED

Theorem trace_step_callee_entry:
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  ALL_DISTINCT (fn_labels callee) /\
  enters_block callee cs t /\ active_inst callee j t ==>
  MEM (TraceVisit ((d,inst.inst_id)::p) (SUC d) callee j t)
    (trace_step orc p d (SUC fuel) ctx inst s)
Proof
  rpt strip_tac >> simp[trace_step_eq] >>
  drule_all trace_blocks_entry_visit >> strip_tac >>
  metis_tac[trace_visit_member]
QED
