Theory dftPacketNativeContinuation
Ancestors
  dftGasFromListTraceDefs venomInstProofs venomExecProofs rich_list arithmetic

Theorem native_trace_continuations:
  (!P D fuel C f inst s. !h p d id fn i t.
    h < LENGTH (trace_step P D fuel C f inst s) /\
    EL h (trace_step P D fuel C f inst s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_step P D fuel C f inst s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest) /\
  (!P D fuel C f bb s. !h p d id fn i t.
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    h < LENGTH (trace_block P D fuel C f bb s) /\
    EL h (trace_block P D fuel C f bb s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_block P D fuel C f bb s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest) /\
  (!P D fuel C f s. !h p d id fn i t.
    h < LENGTH (trace_blocks P D fuel C f s) /\
    EL h (trace_blocks P D fuel C f s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_blocks P D fuel C f s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume native_trace_continuations[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[cj 1 trace_defs] >>
  Cases_on `decode_invoke inst` >> gvs[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> gvs[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> gvs[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED

Resume native_trace_continuations[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 2 trace_defs)]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME head` >>
  drule_then assume_tac trace_block_visit >>
  Cases_on `h`
  >- (gvs[] >> qexists_tac `bb` >> qexists_tac `[]` >> simp[]) >>
  rename1 `SUC k` >>
  gvs[] >>
  Cases_on `k < LENGTH (trace_step P D fuel C f head s)`
  >- (gvs[EL_APPEND] >>
      qpat_x_assum `!h p d id fn i t. _` drule_all >> strip_tac >>
      qexists_tac `bt` >>
      qmatch_goalsub_abbrev_tac `DROP k (ts ++ tail)` >>
      qexists_tac `rest ++ tail` >>
      simp[DROP_APPEND1, Abbr `ts`, APPEND_ASSOC]) >>
  Cases_on `step_inst fuel C head s` >> gvs[] >>
  rename1 `step_inst _ _ _ _ = OK post` >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  drule_all step_preserves_control_flow >> strip_tac >>
  gvs[EL_APPEND, DROP_APPEND2] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume native_trace_continuations[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- gvs[] >>
  rename1 `trace_blocks P D (SUC n) C f s` >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 3 trace_defs)]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[] >>
  qpat_x_assum `h < _` mp_tac >>
  once_rewrite_tac[cj 3 trace_defs] >> simp[] >> strip_tac >>
  rename1 `eval_phis _ _ = OK sp` >>
  drule_all trace_blocks_enter >> disch_then assume_tac >> gvs[] >>
  `sp.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  qmatch_asmsub_abbrev_tac `exec_block n C bb start` >>
  Cases_on `h < LENGTH (trace_block P (SUC D) n C f bb start)`
  >- (gvs[EL_APPEND] >>
      qpat_x_assum `!h p d id fn i t. _` drule_all >> strip_tac >>
      qexists_tac `bt` >>
      qmatch_goalsub_abbrev_tac `DROP h (ts ++ tail)` >>
      qexists_tac `rest ++ tail` >>
      simp[DROP_APPEND1, Abbr `ts`, APPEND_ASSOC, ADD_CLAUSES]) >>
  Cases_on `exec_block n C bb start` >> gvs[] >>
  rename1 `exec_block _ _ _ _ = OK post` >>
  Cases_on `post.vs_halted` >> gvs[] >>
  gvs[EL_APPEND, DROP_APPEND2, ADD_CLAUSES] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Finalise native_trace_continuations

Theorem native_trace_blocks_continuation:
  !P D fuel C f s h p d id fn i t.
    h < LENGTH (trace_blocks P D fuel C f s) /\
    EL h (trace_blocks P D fuel C f s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_blocks P D fuel C f s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest
Proof
  metis_tac[cj 3 native_trace_continuations]
QED
