Theory dftPacketNativeSlice
Ancestors
  dftGasFromListTraceDefs dftIndexedExec rich_list list venomInst venomState

Theorem native_trace_block_prefix_split:
  !k s t.
    s.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) /\
    FOLDR (dft_exec_cons fuel C) OK
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s = OK t ==>
    t.vs_inst_idx = s.vs_inst_idx + k /\
    trace_block p d fuel C fn bb s =
      trace_block p d fuel C fn
        (bb with bb_instructions := TAKE (s.vs_inst_idx + k) bb.bb_instructions) s ++
      trace_block p d fuel C fn bb t
Proof
  Induct_on `k`
  >- (simp[] >> rpt strip_tac >>
      simp[Once trace_defs, get_instruction_def, LENGTH_TAKE]) >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `DROP s.vs_inst_idx bb.bb_instructions =
    EL s.vs_inst_idx bb.bb_instructions ::
    DROP (SUC s.vs_inst_idx) bb.bb_instructions` by
      simp[DROP_CONS_EL] >>
  gvs[TAKE_def, dft_exec_cons_def, AllCaseEqs()] >>
  first_x_assum (qspec_then `t' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (EL s.vs_inst_idx bb.bb_instructions)` by simp[get_instruction_def] >>
  `get_instruction
      (bb with bb_instructions := TAKE (SUC k + s.vs_inst_idx) bb.bb_instructions)
      s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
    simp[get_instruction_def, EL_TAKE] >>
  drule trace_block_visit >>
  disch_then (qspecl_then [`p`,`fuel`,`fn`,`d`,`C`] assume_tac) >>
  qpat_x_assum `get_instruction (_ with bb_instructions := _) _ = _` kall_tac >>
  drule trace_block_visit >>
  disch_then (qspecl_then [`p`,`fuel`,`fn`,`d`,`C`] assume_tac) >>
  gvs[arithmeticTheory.ADD_CLAUSES, APPEND_ASSOC]
QED
