(* Reflect an actual primitive abort through the enclosing oracle run. *)
Theory dftGasToListAbort
Ancestors
  dftGasToListReachWitness dftGasToListFuel dftGasToListTrace
  dftGasOracleDefs venomExecSemantics venomInst venomState venomWf list
  passSimulationDefs

Theorem trace_primitive_abort:
  (!orc p d fuel ctx outer s.
    !p0 d0 fn0 inst t a u.
    MEM (TraceVisit p0 d0 fn0 inst t) (trace_step orc p d fuel ctx outer s) /\
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst t = Abort a u ==>
    ev_step orc p d fuel ctx outer s = Abort a u) /\
  (!orc p d fuel ctx fn bb s.
    !p0 d0 fn0 inst t a u.
    MEM (TraceVisit p0 d0 fn0 inst t) (trace_block orc p d fuel ctx fn bb s) /\
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst t = Abort a u ==>
    ev_block orc p d fuel ctx bb s = Abort a u) /\
  (!orc p d fuel ctx fn s.
    !p0 d0 fn0 inst t a u.
    MEM (TraceVisit p0 d0 fn0 inst t) (trace_blocks orc p d fuel ctx fn s) /\
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst t = Abort a u ==>
    ev_blocks orc p d fuel ctx fn s = Abort a u)
Proof
  ho_match_mp_tac oracle_trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_primitive_abort[step]:
  map_every qx_gen_tac [`orc`, `p`, `d`, `fuel`, `ctx`, `inst`, `s`] >>
  strip_tac >> rpt gen_tac >>
  Cases_on `inst.inst_opcode = GAS`
  >- simp[trace_step_eq] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke inst`
      >- simp[trace_step_eq] >>
      rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
      Cases_on `lookup_function pair0 ctx.ctx_functions`
      >- simp[trace_step_eq] >>
      Cases_on `eval_operands pair1 s`
      >- simp[trace_step_eq] >>
      rename1 `lookup_function pair0 ctx.ctx_functions = SOME callee` >>
      rename1 `eval_operands pair1 s = SOME args` >>
      Cases_on `setup_callee callee args s`
      >- simp[trace_step_eq] >>
      simp[trace_step_eq] >> strip_tac >>
      gvs[] >> first_x_assum drule_all >> strip_tac >>
      simp[ev_step_def]) >>
  simp[trace_step_eq]
QED

Resume trace_primitive_abort[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once trace_block_eq] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME outer` >>
  once_rewrite_tac[trace_block_eq, ev_block_def] >> simp[MEM_APPEND] >>
  strip_tac
  >- (gvs[] >> simp[ev_step_def])
  >- (gvs[] >> first_x_assum drule_all >> strip_tac >> simp[]) >>
  Cases_on `ev_step orc p d fuel ctx outer s` >> gvs[] >>
  Cases_on `is_terminator outer.inst_opcode` >> gvs[] >>
  metis_tac[]
QED

Resume trace_primitive_abort[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  namedCases_on `fuel` ["", "small"]
  >- simp[trace_blocks_zero] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once trace_blocks_eq] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  once_rewrite_tac[trace_blocks_eq, ev_blocks_def] >> simp[MEM_APPEND] >>
  strip_tac
  >- (gvs[] >> first_x_assum drule_all >> strip_tac >> simp[]) >>
  rename1 `eval_phis s bb.bb_instructions = OK s_phi` >>
  qmatch_asmsub_abbrev_tac `ev_block orc p (SUC d) small ctx bb entry` >>
  Cases_on `ev_block orc p (SUC d) small ctx bb entry` >> gvs[] >>
  rename1 `ev_block orc p (SUC d) small ctx bb entry = OK result` >>
  Cases_on `result.vs_halted` >> gvs[] >>
  metis_tac[]
QED

Finalise trace_primitive_abort

Theorem trace_context_primitive_abort:
  MEM (TraceVisit p d fn inst t) (trace_context orc fuel ctx s) /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  step_inst_base inst t = Abort a u ==>
  ev_context orc fuel ctx s = Abort a u
Proof
  Cases_on `ctx.ctx_entry`
  >- simp[trace_context_def] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions`
  >- simp[trace_context_def] >>
  rename1 `lookup_function nm ctx.ctx_functions = SOME entry_fn` >>
  Cases_on `fn_entry_label entry_fn` >>
  simp[trace_context_def, trace_function_def, ev_context_def, ev_function_def] >>
  metis_tac[cj 3 trace_primitive_abort]
QED

Theorem ev_reachable_primitive_abort:
  EVERY wf_function ctx.ctx_functions /\
  ev_reachable orc s ctx p d fn inst t /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  step_inst_base inst t = Abort a u ==>
  !fuel. terminates (ev_context orc fuel ctx s) ==>
    ev_context orc fuel ctx s = Abort a u
Proof
  strip_tac >> drule_all ev_reachable_trace_item >>
  disch_then (qx_choose_then `w` assume_tac) >>
  qx_gen_tac `fuel` >> strip_tac >>
  `w <= w + fuel` by simp[] >>
  drule trace_context_fuel_extension >>
  disch_then (qspecl_then [`s`, `orc`, `ctx`] mp_tac) >>
  rewrite_tac[trace_extension_def] >> strip_tac >>
  `MEM (TraceVisit p d fn inst t) (trace_context orc (w + fuel) ctx s)`
    by metis_tac[MEM_APPEND] >>
  `ev_context orc (w + fuel) ctx s = Abort a u`
    by metis_tac[trace_context_primitive_abort] >>
  `fuel <= w + fuel` by simp[] >>
  drule trace_context_fuel_extension >>
  disch_then (qspecl_then [`s`, `orc`, `ctx`] mp_tac) >>
  rewrite_tac[trace_extension_def] >> strip_tac >>
  Cases_on `ev_context orc fuel ctx s` >> gvs[terminates_def]
QED
