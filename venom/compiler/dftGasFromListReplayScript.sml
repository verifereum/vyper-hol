Theory dftGasFromListReplay
Ancestors
  dftGasFromListReplayBoundary dftGasFromListRestore dftGasFromListTraceDefs
  gasOracleReplay dftGasOracleDefs venomExecSemantics venomState venomInst list

Theorem trace_replay:
  (!p d fuel ctx fn inst s. !orc gs.
    trace_agrees orc (((p,d,inst.inst_id),fn,inst,s)::trace_step p d fuel ctx fn inst s) ==>
    restore_rel gs (step_inst fuel ctx inst s)
      (ev_step orc p d fuel ctx inst (s with vs_gas_readings := gs))) /\
  (!p d fuel ctx fn bb s. !orc gs.
    trace_agrees orc (trace_block p d fuel ctx fn bb s) ==>
    restore_rel gs (exec_block fuel ctx bb s)
      (ev_block orc p d fuel ctx bb (s with vs_gas_readings := gs))) /\
  (!p d fuel ctx fn s. !orc gs.
    trace_agrees orc (trace_blocks p d fuel ctx fn s) ==>
    restore_rel gs (run_blocks fuel ctx fn s)
      (ev_blocks orc p d fuel ctx fn (s with vs_gas_readings := gs)))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_replay[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[trace_agrees_cons] >> strip_tac >>
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[Once step_inst_def, ev_step_def] >>
      `ev_gas (orc (p,d,inst.inst_id)) inst (s with vs_gas_readings := gs) =
       restore_result gs (exec_gas inst s)` by
        (irule ev_gas_restore >> simp[]) >>
      gvs[] >> simp[step_inst_base_def] >>
      Cases_on `exec_gas inst s` >>
      simp[restore_result_def, restore_rel_def]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke"
  >> simp[Once step_inst_def, ev_step_def, step_base_restore]
QED

Resume trace_replay[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (simp[Once exec_block_def] >>
      simp[Once ev_block_def, restore_rel_def]) >>
  rename1 `get_instruction _ _ = SOME inst` >>
  qpat_x_assum `trace_agrees _ _` mp_tac >>
  simp[Once trace_defs, trace_agrees_cons] >> strip_tac >>
  `restore_rel gs (step_inst fuel ctx inst s)
    (ev_step orc p d fuel ctx inst (s with vs_gas_readings := gs))` by
    (first_x_assum irule >> simp[trace_agrees_cons]) >>
  simp[Once exec_block_def] >> simp[Once ev_block_def] >>
  Cases_on `step_inst fuel ctx inst s` >>
  gvs[restore_rel_cases] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (simp[] >> IF_CASES_TAC >> simp[]) >>
  gvs[] >> first_x_assum irule >> simp[]
QED

Resume trace_replay[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel`
  >- (simp[Once run_blocks_def] >> simp[Once ev_blocks_def]) >>
  rename1 `SUC k` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (simp[Once run_blocks_def] >> simp[Once ev_blocks_def]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  assume_tac (Q.INST [`gs` |-> `gs`, `s` |-> `s`,
    `insts` |-> `bb.bb_instructions`] eval_phis_restore) >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- (gvs[restore_rel_cases] >>
      qpat_x_assum `trace_agrees _ _` mp_tac >>
      simp[Once trace_defs, trace_agrees_append] >> strip_tac >>
      first_x_assum (qspec_then `orc` mp_tac) >>
      disch_then (qspec_then `gs` mp_tac) >> simp[] >> strip_tac >>
      simp[Once run_blocks_def] >> simp[Once ev_blocks_def] >>
      Cases_on `exec_block k ctx bb
        (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
      gvs[restore_rel_cases] >>
      rename1 `exec_block _ _ _ _ = OK out` >>
      Cases_on `out.vs_halted` >> gvs[restore_rel_cases] >>
      first_x_assum irule >> simp[]) >>
  gvs[restore_rel_cases] >>
  simp[Once run_blocks_def] >> simp[Once ev_blocks_def, restore_rel_def]
QED

Resume trace_replay[invoke]:
  Cases_on `decode_invoke inst`
  >- simp[Once step_inst_def, ev_step_def, restore_rel_cases] >>
  rename1 `decode_invoke inst = SOME decoded` >>
  PairCases_on `decoded` >>
  Cases_on `lookup_function decoded0 ctx.ctx_functions`
  >- simp[Once step_inst_def, ev_step_def, restore_rel_cases] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands decoded1 s`
  >- simp[Once step_inst_def, ev_step_def, restore_rel_cases] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s`
  >- simp[Once step_inst_def, ev_step_def, gas_setup_callee, restore_rel_cases] >>
  rename1 `setup_callee _ _ _ = SOME cs` >>
  `restore_rel gs (run_blocks fuel ctx callee cs)
     (ev_blocks orc ((d,inst.inst_id)::p) d fuel ctx callee
       (cs with vs_gas_readings := gs))` by
    (first_x_assum irule >> simp[] >>
     qpat_x_assum `trace_agrees _ _` mp_tac >> simp[Once trace_defs]) >>
  simp[Once step_inst_def, ev_step_def, gas_setup_callee] >>
  Cases_on `run_blocks fuel ctx callee cs` >> gvs[restore_rel_cases] >>
  simp[gas_merge_callee, gas_adopt_return, gas_bind_outputs] >>
  rename1 `run_blocks _ _ _ _ = IntRet ret out` >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s out))` >>
  simp[restore_rel_cases]
QED

Finalise trace_replay


Theorem trace_function_replay:
  trace_agrees orc (trace_function fuel ctx fn s) ==>
  restore_rel gs (run_function fuel ctx fn s)
    (ev_function orc fuel ctx fn (s with vs_gas_readings := gs))
Proof
  Cases_on `fn_entry_label fn` >>
  simp[trace_function_def, run_function_def, ev_function_def, restore_rel_cases] >>
  strip_tac >> drule (cj 3 trace_replay) >>
  disch_then (qspec_then `gs` mp_tac) >> simp[]
QED

Theorem trace_context_replay:
  trace_agrees orc (trace_context fuel ctx s) ==>
  restore_rel gs (run_context fuel ctx s)
    (ev_context orc fuel ctx (s with vs_gas_readings := gs))
Proof
  Cases_on `ctx.ctx_entry` >>
  simp[trace_context_def, run_context_def, ev_context_def, restore_rel_cases] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions` >>
  simp[restore_rel_cases] >> strip_tac >>
  drule trace_function_replay >>
  disch_then (qspec_then `gs` mp_tac) >> simp[]
QED

Theorem trace_context_gas_res:
  trace_agrees orc (trace_context fuel ctx s) ==>
  gas_res_rel (run_context fuel ctx s) (ev_context orc fuel ctx s)
Proof
  strip_tac >> irule restore_rel_gas_res >>
  qexists_tac `s.vs_gas_readings` >>
  drule trace_context_replay >>
  disch_then (qspec_then `s.vs_gas_readings` mp_tac) >> simp[]
QED
