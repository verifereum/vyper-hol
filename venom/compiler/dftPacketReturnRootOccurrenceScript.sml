Theory dftPacketReturnRootOccurrence
Ancestors
  gasFocusNativeRootReturn dftGasFromListTraceNames dftGasFromListReadings
  dftGasFromListTraceDefs
  dftPacketNativeContinuation dftPacketReturnNative venomExecSemantics
  venomInst list rich_list arithmetic

Theorem return_trace_block_endpoint[local]:
  !fuel C bb s p d id fn i t ir out.
  MEM ((p,d,id),fn,i,t) (trace_block p d fuel C fn bb s) /\
  i.inst_opcode <> INVOKE /\ step_inst fuel C i t = IntRet ir out ==>
  LAST (trace_block p d fuel C fn bb s) = ((p,d,id),fn,i,t) /\
  exec_block fuel C bb s = IntRet ir out
Proof
  rpt gen_tac >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> strip_tac >> gvs[] >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `MEM _ _` mp_tac >> simp[Once (cj 2 trace_defs)]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME head` >>
  drule_then assume_tac trace_block_visit >>
  Cases_on `((p,d,id),fn,i,t) = ((p,d,head.inst_id),fn,head,s)`
  >- (gvs[] >> simp[Once exec_block_def, trace_step_noninvoke]) >>
  `~MEM ((p,d,id),fn,i,t) (trace_step p d fuel C fn head s)` by
    (strip_tac >>
     `MEM (p,d,id) (MAP FST (trace_step p d fuel C fn head s))` by
       (simp[MEM_MAP] >> qexists_tac `((p,d,id),fn,i,t)` >> simp[]) >>
     metis_tac[trace_step_not_root]) >>
  Cases_on `step_inst fuel C head s` >> gvs[] >>
  rename1 `step_inst fuel C head s = OK post` >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  `LENGTH bb.bb_instructions - SUC s.vs_inst_idx <
   LENGTH bb.bb_instructions - s.vs_inst_idx` by
    (gvs[get_instruction_def] >> decide_tac) >>
  qpat_x_assum `!y. _` (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  simp[] >>
  disch_then (qspec_then `post with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  `trace_block p d fuel C fn bb
    (post with vs_inst_idx := SUC s.vs_inst_idx) <> []` by
    (strip_tac >> gvs[]) >>
  simp[Once exec_block_def] >>
  simp[listTheory.LAST_CONS_cond, LAST_APPEND_NOT_NIL]
QED

Theorem return_trace_blocks_endpoint[local]:
  !fuel p D C fn s d id i t ir out.
  MEM ((p,d,id),fn,i,t) (trace_blocks p D fuel C fn s) /\
  i.inst_opcode <> INVOKE /\ step_inst (D + fuel - d) C i t = IntRet ir out ==>
  LAST (trace_blocks p D fuel C fn s) = ((p,d,id),fn,i,t) /\
  run_blocks fuel C fn s = IntRet ir out
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (qpat_x_assum `MEM _ _` mp_tac >> simp[Once (cj 3 trace_defs)]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions`
  >~ [`eval_phis _ _ = OK sp`]
  >- (qpat_x_assum `MEM _ _` mp_tac >>
      simp[Once (cj 3 trace_defs)] >> disch_tac >>
      qabbrev_tac `start = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
      Cases_on `MEM ((p,d,id),fn,i,t) (trace_block p (SUC D) fuel C fn bb start)`
      >- (drule trace_block_region >>
          simp[block_region_def] >> strip_tac
          >- (gvs[ADD_CLAUSES] >>
              drule_all return_trace_block_endpoint >> strip_tac >>
              gvs[] >> simp[Once (cj 3 trace_defs), Once run_blocks_def, Abbr `start`]) >>
          `LENGTH p = LENGTH (extra ++ (SUC D,call_id)::p)` by metis_tac[] >>
          gvs[]) >>
      Cases_on `exec_block fuel C bb start` >> gvs[] >>
      rename1 `exec_block _ _ _ _ = OK post` >>
      Cases_on `post.vs_halted` >> gvs[] >>
      `LAST (trace_blocks p (SUC D) fuel C fn post) = ((p,d,id),fn,i,t) /\
       run_blocks fuel C fn post = IntRet ir out` by
        (first_x_assum irule >> fs[ADD_CLAUSES]) >>
      `trace_blocks p (SUC D) fuel C fn post <> []` by
        (strip_tac >> gvs[]) >>
      simp[Once (cj 3 trace_defs), LAST_APPEND_NOT_NIL, Once run_blocks_def, Abbr `start`]) >>
  qpat_x_assum `MEM _ _` mp_tac >> simp[Once (cj 3 trace_defs)]
QED
