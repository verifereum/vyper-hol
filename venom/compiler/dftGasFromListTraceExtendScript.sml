Theory dftGasFromListTraceExtend
Ancestors
  dftGasFromListLookup dftGasFromListTracePrefix dftGasFromListTraceDefs
  venomWf venomExecProofs contextCodegenRel contextRawReachable
  venomExecSemantics venomInst venomState list arithmetic

Theorem trace_entered_head:
  wf_function fn /\ enters_block fn s u /\ active_inst fn inst u ==>
  MEM ((p,SUC d,inst.inst_id),fn,inst,u)
    (trace_blocks p d (SUC fuel) ctx fn s)
Proof
  strip_tac >> drule_all entered_active_lookup >> strip_tac >> gvs[] >>
  simp[Once trace_defs] >>
  simp[Once trace_defs]
QED

Theorem trace_context_entry:
  wf_function fn /\ ctx.ctx_entry = SOME nm /\
  lookup_function nm ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (s with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) u /\
  active_inst fn inst u ==>
  !k. ?m. k <= m /\
    MEM (([],1,inst.inst_id),fn,inst,u) (trace_context m ctx s)
Proof
  strip_tac >> gen_tac >> qexists_tac `SUC k` >> simp[] >>
  simp[trace_context_def, trace_function_def] >>
  irule (SRULE [] (Q.INST [`d` |-> `0`] trace_entered_head)) >> simp[]
QED
