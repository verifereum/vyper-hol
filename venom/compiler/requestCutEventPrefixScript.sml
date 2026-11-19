Theory requestCutEventPrefix
Ancestors
  requestCutNativeEventCover dftGasFromListReplay dftGasFromListReplayBoundary
  dftGasFromListTraceDefs dftGasFromListRestore dftGasToListTrace
  dftGasOracleDefs gasOracleReplay venomExecSemantics venomState venomInst
  list rich_list

val nativeItems = ``\ws (rows:list_visit list).
  FLAT (MAP (\((p,d,id),fn,i,s).
    TraceVisit p d fn i (s with vs_gas_readings := ws) ::
    if i.inst_opcode = GAS then [TraceGas (p,d,id)] else []) rows)``;

Theorem visits_prefix_split[local]:
  pre <<= left ++ right ==>
  pre <<= left \/ ?tail. pre = left ++ tail /\ tail <<= right
Proof
  strip_tac >> drule IS_PREFIX_APPEND2 >> strip_tac >> simp[] >>
  disj2_tac >> fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC, APPEND_11]
QED

Theorem visits_prefix_extend[local]:
  pre <<= xs ==> pre <<= xs ++ ys
Proof
  simp[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]
QED

(* Every agreed native prefix is a prefix of the oracle execution's
   mixed visit/GAS log. The oracle may differ after the prefix. *)
Theorem request_cut_native_event_prefix:
  (!p d fuel C fn i s. !orc ws pre.
    pre <<= dftGasFromListTraceDefs$trace_step p d fuel C fn i s /\ trace_agrees orc pre ==>
    ^nativeItems ws pre <<=
      dftGasToListTrace$trace_step orc p d fuel C i (s with vs_gas_readings := ws)) /\
  (!p d fuel C fn bb s. !orc ws pre.
    pre <<= dftGasFromListTraceDefs$trace_block p d fuel C fn bb s /\ trace_agrees orc pre ==>
    ^nativeItems ws pre <<=
      dftGasToListTrace$trace_block orc p d fuel C fn bb (s with vs_gas_readings := ws)) /\
  (!p d fuel C fn s. !orc ws pre.
    pre <<= dftGasFromListTraceDefs$trace_blocks p d fuel C fn s /\ trace_agrees orc pre ==>
    ^nativeItems ws pre <<=
      dftGasToListTrace$trace_blocks orc p d fuel C fn (s with vs_gas_readings := ws))
Proof
  BETA_TAC >> ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume request_cut_native_event_prefix[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (simp[cj 1 trace_defs, trace_step_eq] >>
      Cases_on `decode_invoke i` >> simp[] >>
      rename1 `decode_invoke i = SOME decoded` >> PairCases_on `decoded` >>
      Cases_on `lookup_function decoded0 C.ctx_functions` >> simp[] >>
      rename1 `lookup_function _ _ = SOME callee` >>
      Cases_on `eval_operands decoded1 s` >> simp[] >>
      rename1 `eval_operands _ _ = SOME args` >>
      Cases_on `setup_callee callee args s` >> simp[gas_setup_callee] >>
      metis_tac[]) >>
  simp[trace_step_noninvoke]
QED

Resume request_cut_native_event_prefix[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx` >-
    simp[Once (cj 2 trace_defs)] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `pre` >- simp[] >>
  drule trace_block_visit >>
  disch_then (qspecl_then [`p`, `fuel`, `fn`, `d`, `C`] assume_tac) >>
  simp[trace_agrees_cons] >>
  strip_tac >>
  drule visits_prefix_split >> strip_tac
  >- suspend "block_inside"
  >> suspend "block_after"
QED

Resume request_cut_native_event_prefix[block_inside]:
  gvs[trace_agrees_cons] >>
  once_rewrite_tac[cj 2 oracle_trace_defs] >>
  simp[] >>
  Cases_on `inst.inst_opcode = GAS`
  >- (`inst.inst_opcode <> INVOKE` by simp[] >>
      fs[trace_step_noninvoke, trace_step_eq] >>
      Cases_on `ev_step orc p d fuel C inst (s with vs_gas_readings := ws)` >> simp[]) >>
  `^nativeItems ws t <<=
    dftGasToListTrace$trace_step orc p d fuel C inst (s with vs_gas_readings := ws)` by
    (BETA_TAC >> metis_tac[]) >>
  Cases_on `ev_step orc p d fuel C inst (s with vs_gas_readings := ws)` >>
  simp[] >> metis_tac[visits_prefix_extend]
QED

Resume request_cut_native_event_prefix[block_after]:
  gvs[trace_agrees_cons] >>
  `restore_rel ws (step_inst fuel C inst s)
    (ev_step orc p d fuel C inst (s with vs_gas_readings := ws))` by
    (irule (cj 1 dftGasFromListReplayTheory.trace_replay) >>
     qexists_tac `fn` >> simp[trace_agrees_cons]) >>
  mp_tac (Q.SPECL [`p`, `d`, `fuel`, `C`, `fn`, `inst`, `s`, `orc`, `ws`]
    (cj 1 request_cut_native_event_trace)) >>
  simp[] >> strip_tac >>
  once_rewrite_tac[cj 2 oracle_trace_defs] >>
  simp[MAP_APPEND, FLAT_APPEND, APPEND_ASSOC] >>
  Cases_on `step_inst fuel C inst s` >> gvs[restore_rel_cases] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  Cases_on `inst.inst_opcode = GAS` >> gvs[APPEND_ASSOC] >>
  metis_tac[]
QED

Resume request_cut_native_event_prefix[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `fuel` >- simp[] >>
  rename1 `SUC f` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >-
    simp[Once (cj 3 trace_defs)] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  assume_tac (Q.INST [`gs` |-> `ws`, `s` |-> `s`,
    `insts` |-> `bb.bb_instructions`] eval_phis_restore) >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[restore_rel_cases] >>
  TRY (simp[Once (cj 3 trace_defs)] >> NO_TAC) >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  qabbrev_tac `u = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  `dftGasFromListTraceDefs$trace_blocks p d (SUC f) C fn s =
    dftGasFromListTraceDefs$trace_block p (SUC d) f C fn bb u ++
    (case exec_block f C bb u of
      OK out => if out.vs_halted then [] else dftGasFromListTraceDefs$trace_blocks p (SUC d) f C fn out
    | _ => [])` by simp[Once (cj 3 trace_defs), Abbr `u`] >>
  simp[] >> strip_tac >>
  drule visits_prefix_split >> strip_tac
  >- suspend "blocks_inside"
  >> suspend "blocks_after"
QED

Resume request_cut_native_event_prefix[blocks_inside]:
  `^nativeItems ws pre <<=
    dftGasToListTrace$trace_block orc p (SUC d) f C fn bb (u with vs_gas_readings := ws)` by
    (qpat_assum `!orc rs xs. xs <<= dftGasFromListTraceDefs$trace_block _ _ _ _ _ _ u /\ _ ==> _`
       (qspecl_then [`orc`, `ws`, `pre`] mp_tac) >> simp[Abbr `u`]) >>
  once_rewrite_tac[cj 3 oracle_trace_defs] >>
  simp[Abbr `u`] >> irule visits_prefix_extend >> simp[]
QED

Resume request_cut_native_event_prefix[blocks_after]:
  gvs[] >>
  `restore_rel ws (run_block_non_phis f C bb u)
    (ev_block orc p (SUC d) f C bb (u with vs_gas_readings := ws))` by
    (irule (cj 2 dftGasFromListReplayTheory.trace_replay) >> qexists_tac `fn` >> simp[]) >>
  mp_tac (Q.SPECL [`p`, `SUC d`, `f`, `C`, `fn`, `bb`, `u`, `orc`, `ws`]
    (cj 2 request_cut_native_event_trace)) >>
  simp[] >> strip_tac >>
  once_rewrite_tac[cj 3 oracle_trace_defs] >>
  Cases_on `run_block_non_phis f C bb u` >>
  gvs[MAP_APPEND, FLAT_APPEND, restore_rel_cases, Abbr `u`] >>
  Cases_on `v.vs_halted` >> gvs[] >> metis_tac[]
QED

Finalise request_cut_native_event_prefix

Theorem request_cut_native_context_event_prefix:
  pre <<= dftGasFromListTraceDefs$trace_context fuel C
    (s with vs_gas_readings := filling) /\ trace_agrees orc pre ==>
  ^nativeItems s.vs_gas_readings pre <<=
    dftGasToListTrace$trace_context orc fuel C s
Proof
  Cases_on `C.ctx_entry` >> simp[dftGasFromListTraceDefsTheory.trace_context_def,
    dftGasToListTraceTheory.trace_context_def, trace_events_def] >>
  rename1 `C.ctx_entry = SOME name` >>
  Cases_on `lookup_function name C.ctx_functions` >> simp[] >>
  rename1 `lookup_function name C.ctx_functions = SOME fn` >>
  Cases_on `fn_entry_label fn` >> simp[dftGasFromListTraceDefsTheory.trace_function_def,
    dftGasToListTraceTheory.trace_function_def] >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  qspecl_then [`[]`, `0`, `fuel`, `C`, `fn`,
    `s with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0;
        vs_gas_readings := filling|>`, `orc`, `s.vs_gas_readings`, `pre`]
    mp_tac (cj 3 request_cut_native_event_prefix) >> simp[]
QED
