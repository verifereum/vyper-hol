Theory dftGasFromListReadings
Ancestors
  dftGasFromListTraceDefs gasCount gasOracleReplay venomExecSemantics
  venomInst venomState list rich_list arithmetic

Theorem trace_gas_append[simp]:
  trace_gas (xs ++ ys) = trace_gas xs ++ trace_gas ys
Proof
  simp[trace_gas_def, MAP_APPEND, FLAT_APPEND]
QED

Theorem trace_gas_cons[simp]:
  trace_gas (v::xs) = visit_gas v ++ trace_gas xs
Proof
  simp[trace_gas_def]
QED

Theorem trace_gas_nil[simp]:
  trace_gas [] = []
Proof
  simp[trace_gas_def]
QED

Theorem trace_gas_lengths:
  (!p d fuel ctx fn inst s.
    LENGTH (visit_gas ((p,d,inst.inst_id),fn,inst,s) ++
      trace_gas (trace_step p d fuel ctx fn inst s)) = gas_count_step fuel ctx inst s) /\
  (!p d fuel ctx fn bb s.
    LENGTH (trace_gas (trace_block p d fuel ctx fn bb s)) = gas_count_block fuel ctx bb s) /\
  (!p d fuel ctx fn s.
    LENGTH (trace_gas (trace_blocks p d fuel ctx fn s)) = gas_count_blocks fuel ctx fn s)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_gas_lengths[step]:
  rpt gen_tac >> strip_tac >>
  simp[cj 1 trace_defs, Once gas_count_step_def, visit_gas_def] >>
  Cases_on `inst.inst_opcode = GAS` >> simp[] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> simp[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> simp[] >>
  metis_tac[]
QED

Resume trace_gas_lengths[block]:
  rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once (cj 2 trace_defs), Once gas_count_block_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  once_rewrite_tac[cj 2 trace_defs, gas_count_block_def] >>
  simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  metis_tac[]
QED

Resume trace_gas_lengths[blocks]:
  rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- simp[Once gas_count_blocks_def] >>
  rename1 `SUC k` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once (cj 3 trace_defs), Once gas_count_blocks_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[Once (cj 3 trace_defs), Once gas_count_blocks_def] >>
  rename1 `eval_phis _ _ = OK sp` >>
  Cases_on `exec_block k ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[] >>
  rename1 `exec_block _ _ _ _ = OK t` >>
  Cases_on `t.vs_halted` >> simp[] >> metis_tac[]
QED

Finalise trace_gas_lengths

Theorem trace_gas_readings:
  (!p d fuel ctx fn inst s.
    MAP SND (visit_gas ((p,d,inst.inst_id),fn,inst,s) ++
      trace_gas (trace_step p d fuel ctx fn inst s)) =
    gas_prefix (gas_count_step fuel ctx inst s) s.vs_gas_readings) /\
  (!p d fuel ctx fn bb s.
    MAP SND (trace_gas (trace_block p d fuel ctx fn bb s)) =
    gas_prefix (gas_count_block fuel ctx bb s) s.vs_gas_readings) /\
  (!p d fuel ctx fn s.
    MAP SND (trace_gas (trace_blocks p d fuel ctx fn s)) =
    gas_prefix (gas_count_blocks fuel ctx fn s) s.vs_gas_readings)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_gas_readings[step]:
  rpt gen_tac >> strip_tac >>
  simp[cj 1 trace_defs, Once gas_count_step_def, visit_gas_def] >>
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[] >> Cases_on `s.vs_gas_readings` >> simp[gas_prefix_def] >> EVAL_TAC) >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> simp[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> simp[] >>
  metis_tac[gas_setup_callee_readings]
QED

Resume trace_gas_readings[block]:
  rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once (cj 2 trace_defs), Once gas_count_block_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  once_rewrite_tac[cj 2 trace_defs, gas_count_block_def] >>
  fs[MAP_APPEND] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst _ _ _ _ = OK t` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  `t.vs_gas_readings = DROP (gas_count_step fuel ctx inst s) s.vs_gas_readings` by
    (mp_tac (cj 1 gas_count_suffix) >>
     disch_then (qspecl_then [`fuel`, `ctx`, `inst`, `s`] mp_tac) >>
     simp[gas_count_suffix_def]) >>
  gvs[] >> metis_tac[gas_prefix_add, ADD_COMM, APPEND_ASSOC]
QED

Resume trace_gas_readings[blocks]:
  rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- simp[Once gas_count_blocks_def] >>
  rename1 `SUC k` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once (cj 3 trace_defs), Once gas_count_blocks_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[Once (cj 3 trace_defs), Once gas_count_blocks_def] >>
  rename1 `eval_phis _ _ = OK sp` >>
  `sp.vs_gas_readings = s.vs_gas_readings` by metis_tac[gas_count_phis_ok] >>
  fs[MAP_APPEND] >>
  Cases_on `run_block_non_phis k ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[] >>
  rename1 `run_block_non_phis _ _ _ _ = OK t` >>
  Cases_on `t.vs_halted` >> simp[] >>
  `t.vs_gas_readings = DROP
     (gas_count_block k ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
     s.vs_gas_readings` by
    (mp_tac (cj 2 gas_count_suffix) >>
     disch_then (qspecl_then [`k`, `ctx`, `bb`,
       `sp with vs_inst_idx := phi_prefix_length bb.bb_instructions`] mp_tac) >>
     simp[gas_count_suffix_def]) >>
  gvs[] >> metis_tac[gas_prefix_add, ADD_COMM]
QED

Finalise trace_gas_readings

Theorem gas_prefix_genlist:
  gas_prefix n rs = GENLIST (\k. if k < LENGTH rs then EL k rs else 0w) n
Proof
  simp[LIST_EQ_REWRITE, gas_prefix_def, EL_GENLIST] >>
  rpt strip_tac >> simp[EL_TAKE, EL_APPEND_EQN, EL_REPLICATE]
QED

Theorem trace_context_readings:
  MAP SND (trace_gas (trace_context fuel ctx s)) =
  gas_prefix (LENGTH (trace_gas (trace_context fuel ctx s))) s.vs_gas_readings
Proof
  simp[trace_context_def, trace_function_def] >>
  Cases_on `ctx.ctx_entry` >> simp[] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions` >> simp[] >>
  rename1 `lookup_function _ _ = SOME fn` >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  rewrite_tac[cj 3 trace_gas_lengths, cj 3 trace_gas_readings] >> simp[]
QED

Theorem trace_context_nonzero_bound:
  k < LENGTH (trace_gas (trace_context fuel ctx s)) /\
  SND (EL k (trace_gas (trace_context fuel ctx s))) <> 0w ==>
  k < LENGTH s.vs_gas_readings
Proof
  strip_tac >>
  mp_tac trace_context_readings >>
  simp[gas_prefix_genlist, LIST_EQ_REWRITE] >>
  disch_then (qspec_then `k` mp_tac) >>
  simp[EL_MAP, EL_GENLIST] >>
  Cases_on `k < LENGTH s.vs_gas_readings` >> simp[]
QED
