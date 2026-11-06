Theory dftGasToListReachTrace
Ancestors
  dftGasToListReachBoundary dftGasToListFuel dftGasToListTrace
  dftGasOracleDefs contextCodegenRel venomExecProofs venomExecSemantics list

Theorem trace_block_initial_visit:
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  MEM (n,p,d,fn,inst,s)
    (trace_visits n (trace_block orc p d fuel ctx fn bb s))
Proof
  simp[Once trace_block_eq, trace_visits_def]
QED

Theorem trace_blocks_entry_visit:
  ALL_DISTINCT (fn_labels fn) /\ enters_block fn s t /\ active_inst fn inst t ==>
  MEM (n,p,SUC d,fn,inst,t)
    (trace_visits n (trace_blocks orc p d (SUC fuel) ctx fn s))
Proof
  rpt strip_tac >> drule_all active_inst_lookup_distinct >> strip_tac >>
  gvs[enters_block_def] >>
  drule eval_phis_preserves_current_bb >> strip_tac >> gvs[] >>
  simp[Once trace_blocks_eq, trace_visits_append] >>
  disj1_tac >> irule trace_block_initial_visit >> simp[]
QED

Theorem trace_context_entry_visit:
  ALL_DISTINCT (fn_labels fn) /\ ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (s with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  active_inst fn inst t ==>
  MEM (0,[],1,fn,inst,t) (trace_visits 0 (trace_context orc (SUC fuel) ctx s))
Proof
  rpt strip_tac >> simp[trace_context_def, trace_function_def] >>
  irule (SRULE [] (Q.INST [`d` |-> `0`] trace_blocks_entry_visit)) >> simp[]
QED
