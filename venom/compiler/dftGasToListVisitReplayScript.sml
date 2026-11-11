Theory dftGasToListVisitReplay
Ancestors
  dftGasToListVisitReplayBoundary dftGasToListReplay dftGasToListAgreement
  dftGasToListTrace dftGasToListVisitEdge dftGasOracleDefs gasOracleReplay contextRawReachable
  contextCodegenRel contextCodegenRelProps venomExecSemantics venomExecProofs
  stepWriteFootprintBase list rich_list arithmetic

Theorem trace_visit_replay:
  (!orc p d fuel ctx inst s vs0 caller ws.
    raw_reachable vs0 ctx caller inst (s with vs_gas_readings := ws) /\
    active_inst caller inst s /\
    agrees orc ws (trace_events (trace_step orc p d fuel ctx inst s)) ==>
    visits_reachable vs0 ctx ws (trace_step orc p d fuel ctx inst s)) /\
  (!orc p d fuel ctx fn bb s vs0 ws.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    head_reachable vs0 ctx fn s ws /\
    agrees orc ws (trace_events (trace_block orc p d fuel ctx fn bb s)) ==>
    visits_reachable vs0 ctx ws (trace_block orc p d fuel ctx fn bb s) /\
    (!u. ev_block orc p d fuel ctx bb s = OK u /\ ~u.vs_halted ==>
      entry_reachable vs0 ctx fn u
        (DROP (LENGTH (trace_events (trace_block orc p d fuel ctx fn bb s))) ws))) /\
  (!orc p d fuel ctx fn s vs0 ws.
    entry_reachable vs0 ctx fn s ws /\
    agrees orc ws (trace_events (trace_blocks orc p d fuel ctx fn s)) ==>
    visits_reachable vs0 ctx ws (trace_blocks orc p d fuel ctx fn s))
Proof
  ho_match_mp_tac oracle_trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_visit_replay[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = GAS`
  >- simp[trace_step_eq] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  simp[trace_step_eq]
QED

Resume trace_visit_replay[invoke]:
  qpat_x_assum `agrees _ _ _` mp_tac >> simp[trace_step_eq] >>
  Cases_on `decode_invoke inst`
  >- simp[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions`
  >- simp[] >>
  rename1 `lookup_function pair0 ctx.ctx_functions = SOME callee` >>
  Cases_on `eval_operands pair1 s`
  >- simp[] >>
  rename1 `eval_operands pair1 s = SOME args` >>
  Cases_on `setup_callee callee args s`
  >- simp[] >>
  rename1 `setup_callee callee args s = SOME cs` >>
  simp[] >> strip_tac >>
  drule_all entry_reachable_callee >> strip_tac >>
  first_x_assum irule >> simp[]
QED
Resume trace_visit_replay[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  once_rewrite_tac[trace_block_eq] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once ev_block_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  simp[] >> strip_tac >>
  `active_inst fn inst s` by (irule lookup_instruction_active >> simp[]) >>
  `raw_reachable vs0 ctx fn inst (s with vs_gas_readings := ws)` by
    metis_tac[head_reachable_def] >>
  Cases_on `ev_step orc p d fuel ctx inst s` >>
  simp[trace_events_def, trace_events_append, agrees_append,
       visits_reachable_append, Once ev_block_def] >>
  qpat_x_assum `agrees _ _ _` mp_tac >>
  simp[trace_events_def, trace_events_append, agrees_append] >> strip_tac >>
  `visits_reachable vs0 ctx ws (trace_step orc p d fuel ctx inst s)` by
    (qpat_x_assum `!inst'. _` irule >> simp[] >> metis_tac[]) >>
  simp[] >>
  TRY (rename1 `ev_step _ _ _ _ _ _ _ = OK u0` >>
       suspend "block_ok" >> NO_TAC) >>
  simp[]
QED
Resume trace_visit_replay[block_ok]:
  drule (cj 1 trace_replay) >>
  simp[] >> strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (gvs[trace_events_def, trace_events_append, agrees_append] >>
      Cases_on `u0.vs_halted` >> simp[] >> rpt strip_tac >> gvs[] >>
      drule_all entry_reachable_jump >> simp[]) >>
  gvs[trace_events_def, trace_events_append, agrees_append] >>
  drule_all head_reachable_next >> strip_tac >>
  drule_all ev_step_nonterm_current_bb >> strip_tac >>
  qpat_x_assum `!vs0' ws'. _` (qspecl_then
    [`vs0`, `DROP (LENGTH (trace_events (trace_step orc p d fuel ctx inst s))) ws`] mp_tac) >>
  simp[DROP_DROP_T, ADD_COMM]
QED
Resume trace_visit_replay[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `fuel`
  >- simp[trace_blocks_eq] >>
  once_rewrite_tac[trace_blocks_eq] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> simp[] >>
  TRY (rename1 `eval_phis _ _ = OK sp` >> suspend "blocks_phi" >> NO_TAC)
QED
Resume trace_visit_replay[blocks_phi]:
  strip_tac >> drule_all replay_block_entry_geometry >> strip_tac >>
  `head_reachable vs0 ctx fn
     (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) ws` by
    metis_tac[entry_reachable_def] >>
  gvs[] >>
  Cases_on `ev_block orc p (SUC d) n ctx bb
     (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  qpat_x_assum `agrees _ _ _` mp_tac >>
  simp[trace_events_append, agrees_append, visits_reachable_append] >>
  strip_tac >>
  Cases_on `v.vs_halted` >> gvs[] >>
  qpat_x_assum `!vs0' ws'. _` drule_all >> strip_tac >>
  qpat_x_assum `!vs0 ws. _` irule >> simp[]
QED
Finalise trace_visit_replay

Theorem replay_context_visit:
  agrees orc ws (trace_events (trace_context orc fuel ctx s)) /\
  MEM (n,p,d,fn,inst,t) (trace_visits 0 (trace_context orc fuel ctx s)) ==>
  raw_reachable (s with vs_gas_readings := ws) ctx fn inst
    (t with vs_gas_readings := DROP n ws)
Proof
  simp[trace_context_def, trace_function_def] >>
  Cases_on `ctx.ctx_entry`
  >- simp[trace_visits_def] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions`
  >- simp[trace_visits_def] >>
  rename1 `lookup_function nm ctx.ctx_functions = SOME entryfn` >>
  Cases_on `fn_entry_label entryfn`
  >- simp[trace_visits_def] >>
  rename1 `fn_entry_label entryfn = SOME lbl` >>
  simp[] >> strip_tac >>
  drule_all entry_reachable_context >>
  disch_then (qspecl_then [`s`, `ws`] assume_tac) >>
  drule_all (cj 3 trace_visit_replay) >>
  simp[visits_reachable_def] >> metis_tac[]
QED
