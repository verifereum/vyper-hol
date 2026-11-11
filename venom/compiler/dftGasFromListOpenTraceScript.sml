Theory dftGasFromListOpenTrace
Ancestors
  dftGasFromListTracePrefix dftGasFromListTraceDefs venomExecProofs
  venomExecSemantics venomInst venomState list arithmetic

Definition open_trace_def:
  open_trace p d k ctx fn bb t =
    trace_block p d k ctx fn bb t ++
    (case exec_block k ctx bb t of
       OK u => if u.vs_halted then [] else trace_blocks p d k ctx fn u
     | _ => [])
End

Theorem open_trace_next:
  get_instruction bb t.vs_inst_idx = SOME i /\
  step_inst k ctx i t = OK u /\ ~is_terminator i.inst_opcode ==>
  open_trace p d k ctx fn bb t =
    ((p,d,i.inst_id),fn,i,t)::
    (trace_step p d k ctx fn i t ++
     open_trace p d k ctx fn bb (u with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  strip_tac >> rewrite_tac[open_trace_def] >>
  simp[Once trace_defs] >> simp[Once exec_block_def, APPEND_ASSOC]
QED

Theorem trace_blocks_open:
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis t bb.bb_instructions = OK sp ==>
  trace_blocks p d (SUC k) ctx fn t =
    open_trace p (SUC d) k ctx fn bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >> simp[Once trace_defs, open_trace_def]
QED

Theorem open_trace_mono:
  n <= m /\ MEM v (open_trace p d n ctx fn bb t) ==>
  MEM v (open_trace p d m ctx fn bb t)
Proof
  simp[open_trace_def, MEM_APPEND] >> strip_tac
  >- (drule (cj 2 trace_prefix) >>
      disch_then (qspecl_then [`p`,`d`,`ctx`,`fn`,`bb`,`t`] strip_assume_tac) >>
      simp[]) >>
  Cases_on `exec_block n ctx bb t` >> gvs[] >>
  rename1 `exec_block n ctx bb t = OK out` >>
  Cases_on `out.vs_halted` >> gvs[] >>
  `exec_block m ctx bb t = OK out` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  simp[] >> drule (cj 3 trace_prefix) >>
  disch_then (qspecl_then [`p`,`d`,`ctx`,`fn`,`out`] strip_assume_tac) >> simp[]
QED
