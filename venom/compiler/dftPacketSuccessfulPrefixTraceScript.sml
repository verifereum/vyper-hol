Theory dftPacketSuccessfulPrefixTrace
Ancestors
  dftGasFromListTracePrefix dftIndexedExec venomExecProofs dftGasFromListReadings
  dftGasFromListTraceDefs venomInst venomState list rich_list arithmetic

Theorem dft_packet_successful_prefix_trace_stable:
  !q s u n m.
    s.vs_inst_idx + q <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE q (DROP s.vs_inst_idx bb.bb_instructions)) /\
    FOLDR (dft_exec_cons n C) OK
      (TAKE q (DROP s.vs_inst_idx bb.bb_instructions)) s = OK u /\
    n <= m ==>
    trace_block a e m C fn
      (bb with bb_instructions := TAKE (s.vs_inst_idx + q) bb.bb_instructions) s =
    trace_block a e n C fn
      (bb with bb_instructions := TAKE (s.vs_inst_idx + q) bb.bb_instructions) s
Proof
  Induct_on `q`
  >- (simp[] >> rpt strip_tac >>
      once_rewrite_tac[cj 2 trace_defs] >>
      simp[get_instruction_def, LENGTH_TAKE]) >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `DROP s.vs_inst_idx bb.bb_instructions =
    EL s.vs_inst_idx bb.bb_instructions ::
    DROP (SUC s.vs_inst_idx) bb.bb_instructions` by simp[DROP_CONS_EL] >>
  gvs[TAKE_def, dft_exec_cons_def, AllCaseEqs()] >>
  rename1 `step_inst n C _ s = OK post` >>
  `step_inst m C (EL s.vs_inst_idx bb.bb_instructions) s = OK post` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  `trace_step a e m C fn (EL s.vs_inst_idx bb.bb_instructions) s =
   trace_step a e n C fn (EL s.vs_inst_idx bb.bb_instructions) s` by
    (irule (cj 1 trace_stable) >> simp[]) >>
  first_x_assum (qspecl_then
    [`post with vs_inst_idx := SUC s.vs_inst_idx`, `u`, `n`, `m`] mp_tac) >>
  simp[] >> strip_tac >>
  `get_instruction
      (bb with bb_instructions := TAKE (SUC q + s.vs_inst_idx) bb.bb_instructions)
      s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
    simp[get_instruction_def, EL_TAKE] >>
  once_rewrite_tac[cj 2 trace_defs] >>
  gvs[arithmeticTheory.ADD_CLAUSES]
QED

Theorem dft_packet_successful_prefix_gas_keys:
  !q s u i.
    s.vs_inst_idx + q <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE q (DROP s.vs_inst_idx bb.bb_instructions)) /\
    FOLDR (dft_exec_cons n C) OK
      (TAKE q (DROP s.vs_inst_idx bb.bb_instructions)) s = OK u /\
    MEM i (TAKE q (DROP s.vs_inst_idx bb.bb_instructions)) /\
    i.inst_opcode = GAS ==>
    ?w. MEM ((a,e,i.inst_id),w)
      (trace_gas (trace_block a e n C fn
        (bb with bb_instructions := TAKE (s.vs_inst_idx + q) bb.bb_instructions) s))
Proof
  Induct_on `q` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `DROP s.vs_inst_idx bb.bb_instructions =
    EL s.vs_inst_idx bb.bb_instructions ::
    DROP (SUC s.vs_inst_idx) bb.bb_instructions` by simp[DROP_CONS_EL] >>
  gvs[TAKE_def, dft_exec_cons_def, AllCaseEqs()] >>
  rename1 `step_inst n C _ s = OK post` >>
  `get_instruction
      (bb with bb_instructions := TAKE (SUC q + s.vs_inst_idx) bb.bb_instructions)
      s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
    simp[get_instruction_def, EL_TAKE] >>
  once_rewrite_tac[cj 2 trace_defs] >> simp[]
  >- (simp[visit_gas_def] >> metis_tac[]) >>
  first_x_assum (qspecl_then
    [`post with vs_inst_idx := SUC s.vs_inst_idx`, `u`, `i`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >> metis_tac[]
QED
