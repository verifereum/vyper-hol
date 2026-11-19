Theory requestCutNativeEventCover
Ancestors
  dftGasFromListReadings dftGasFromListReplay dftGasFromListRestore
  dftGasFromListReplayBoundary dftGasFromListTraceDefs dftGasToListFuel
  dftGasToListVisitReplay dftGasToListReachWitness dftGasToListAgreement
  dftGasToListTrace dftGasOracleKeyReplay dftGasFromListTraceNames
  dftGasOracleDefs gasOracleReplay contextCodegenRel dftCorrectness
  dftPacketObservedGasHead dftGasFromListUnion
  venomExecSemantics venomState venomInst passSimulationDefs list rich_list

val nativeTraceItems = ``\ws (rows:list_visit list).
  FLAT (MAP (\((p,d,id),fn,i,s).
    TraceVisit p d fn i (s with vs_gas_readings := ws) ::
    if i.inst_opcode = GAS then [TraceGas (p,d,id)] else []) rows)``;

(* Replaying the native tape preserves the entire mixed visit and GAS log. *)
Theorem request_cut_native_event_trace:
  (!p d fuel C fn i s. !orc ws.
    trace_agrees orc (dftGasFromListTraceDefs$trace_step p d fuel C fn i s) ==>
    dftGasToListTrace$trace_step orc p d fuel C i (s with vs_gas_readings := ws) =
      (if i.inst_opcode = GAS then [TraceGas (p,d,i.inst_id)] else []) ++
      ^nativeTraceItems ws (dftGasFromListTraceDefs$trace_step p d fuel C fn i s)) /\
  (!p d fuel C fn bb s. !orc ws.
    trace_agrees orc (dftGasFromListTraceDefs$trace_block p d fuel C fn bb s) ==>
    dftGasToListTrace$trace_block orc p d fuel C fn bb (s with vs_gas_readings := ws) =
      ^nativeTraceItems ws (dftGasFromListTraceDefs$trace_block p d fuel C fn bb s)) /\
  (!p d fuel C fn s. !orc ws.
    trace_agrees orc (dftGasFromListTraceDefs$trace_blocks p d fuel C fn s) ==>
    dftGasToListTrace$trace_blocks orc p d fuel C fn (s with vs_gas_readings := ws) =
      ^nativeTraceItems ws (dftGasFromListTraceDefs$trace_blocks p d fuel C fn s))
Proof
  BETA_TAC >> ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume request_cut_native_event_trace[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `i.inst_opcode = GAS`
  >- (`i.inst_opcode <> INVOKE` by simp[] >>
      simp[trace_step_noninvoke, trace_step_eq]) >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (simp[cj 1 trace_defs, trace_step_eq] >>
      Cases_on `decode_invoke i` >> simp[] >>
      rename1 `decode_invoke i = SOME decoded` >> PairCases_on `decoded` >>
      Cases_on `lookup_function decoded0 C.ctx_functions` >> simp[] >>
      rename1 `lookup_function _ _ = SOME callee` >>
      Cases_on `eval_operands decoded1 s` >> simp[] >>
      rename1 `eval_operands _ _ = SOME args` >>
      Cases_on `setup_callee callee args s` >> simp[gas_setup_callee]) >>
  simp[trace_step_noninvoke, trace_step_eq]
QED

Resume request_cut_native_event_trace[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx` >-
    simp[Once (cj 2 trace_defs), Once (cj 2 oracle_trace_defs)] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  drule trace_block_visit >>
  disch_then (qspecl_then [`p`, `fuel`, `fn`, `d`, `C`] assume_tac) >>
  qpat_x_assum `trace_agrees _ _` mp_tac >>
  qpat_assum `trace_block _ _ _ _ _ _ _ = _` (fn eq => PURE_REWRITE_TAC [eq]) >>
  simp[trace_agrees_cons] >> strip_tac >>
  `restore_rel ws (step_inst fuel C inst s)
    (ev_step orc p d fuel C inst (s with vs_gas_readings := ws))` by
    (irule (cj 1 dftGasFromListReplayTheory.trace_replay) >>
     qexists_tac `fn` >> simp[trace_agrees_cons]) >>
  once_rewrite_tac[cj 2 oracle_trace_defs] >>
  simp[MAP_APPEND, FLAT_APPEND] >>
  Cases_on `step_inst fuel C inst s` >> gvs[restore_rel_cases] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  simp[visit_gas_def] >> Cases_on `inst.inst_opcode = GAS` >> simp[]
QED

Resume request_cut_native_event_trace[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >-
    simp[Once (cj 3 trace_defs), Once (cj 3 oracle_trace_defs)] >>
  rename1 `SUC f` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >-
    simp[Once (cj 3 trace_defs), Once (cj 3 oracle_trace_defs)] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  assume_tac (Q.INST [`gs` |-> `ws`, `s` |-> `s`,
    `insts` |-> `bb.bb_instructions`] eval_phis_restore) >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[restore_rel_cases] >>
  TRY (simp[Once (cj 3 trace_defs), Once (cj 3 oracle_trace_defs)] >> NO_TAC) >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  qabbrev_tac `u = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  `dftGasFromListTraceDefs$trace_blocks p d (SUC f) C fn s =
    dftGasFromListTraceDefs$trace_block p (SUC d) f C fn bb u ++
    (case exec_block f C bb u of
      OK out => if out.vs_halted then [] else dftGasFromListTraceDefs$trace_blocks p (SUC d) f C fn out
    | _ => [])` by simp[Once (cj 3 trace_defs), Abbr `u`] >>
  qpat_x_assum `trace_agrees _ _` mp_tac >>
  qpat_assum `trace_blocks p d (SUC f) C fn s = _` (fn eq => PURE_REWRITE_TAC [eq]) >>
  simp[Once (cj 3 oracle_trace_defs), trace_agrees_append, MAP_APPEND, FLAT_APPEND] >> strip_tac >>
  `restore_rel ws (exec_block f C bb u)
    (ev_block orc p (SUC d) f C bb (u with vs_gas_readings := ws))` by
    (irule (cj 2 dftGasFromListReplayTheory.trace_replay) >> metis_tac[]) >>
  Cases_on `exec_block f C bb u` >> gvs[restore_rel_cases] >>
  Cases_on `v.vs_halted` >> gvs[Abbr `u`]
QED

Finalise request_cut_native_event_trace

Theorem native_event_trace_gas_keys[local]:
  !rows ws. trace_events (^nativeTraceItems ws rows) = MAP FST (trace_gas rows)
Proof
  BETA_TAC >> Induct >> simp[trace_events_def] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  Cases_on `h4.inst_opcode = GAS` >>
  simp[trace_events_def, trace_events_append, trace_gas_cons, visit_gas_def] >>
  Cases_on `h5.vs_gas_readings` >> simp[]
QED

Theorem native_blocks_oracle_agreement[local]:
  trace_agrees orc (dftGasFromListTraceDefs$trace_blocks p d fuel C fn
     (u with vs_gas_readings := rds)) ==>
  agrees orc rds (trace_events (dftGasToListTrace$trace_blocks orc p d fuel C fn u))
Proof
  strip_tac >>
  qabbrev_tac `s = u with vs_gas_readings := rds` >>
  qabbrev_tac `hist = trace_gas (dftGasFromListTraceDefs$trace_blocks p d fuel C fn s)` >>
  `trace_events (dftGasToListTrace$trace_blocks orc p d fuel C fn u) = MAP FST hist` by
    (qspecl_then [`p`, `d`, `fuel`, `C`, `fn`, `s`, `orc`, `u.vs_gas_readings`] mp_tac
       (cj 3 request_cut_native_event_trace) >>
     simp[Abbr `s`, Abbr `hist`, venom_state_component_equality,
          BETA_RULE native_event_trace_gas_keys]) >>
  `MAP SND hist = gas_prefix (LENGTH hist) rds` by
    simp[Abbr `hist`, cj 3 trace_gas_readings, cj 3 trace_gas_lengths, Abbr `s`] >>
  simp[agrees_def, EL_MAP] >> rpt strip_tac >>
  `EVERY (\(key,w). orc key = w) hist` by fs[trace_agrees_def, Abbr `hist`] >>
  `orc (FST (EL i hist)) = SND (EL i hist)` by
    (qpat_x_assum `EVERY _ hist` mp_tac >>
     simp[EVERY_EL] >> disch_then (qspec_then `i` mp_tac) >>
     simp[] >> Cases_on `EL i hist` >> simp[]) >>
  `EL i (MAP SND hist) = padded_reading rds i` by
    (qpat_assum `MAP SND hist = _` SUBST1_TAC >>
     simp[gas_prefix_genlist, EL_GENLIST, padded_reading_def]) >>
  qpat_x_assum `EL i (MAP SND hist) = _` (SUBST1_TAC o SYM) >>
  simp[EL_MAP]
QED

Theorem native_context_oracle_agreement[local]:
  trace_agrees orc (dftGasFromListTraceDefs$trace_context fuel C
     (v with vs_gas_readings := rds)) ==>
  agrees orc rds (trace_events (dftGasToListTrace$trace_context orc fuel C v))
Proof
  Cases_on `C.ctx_entry` >> simp[dftGasFromListTraceDefsTheory.trace_context_def,
    dftGasToListTraceTheory.trace_context_def, trace_events_def] >>
  rename1 `C.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm C.ctx_functions` >> simp[trace_events_def] >>
  rename1 `lookup_function nm C.ctx_functions = SOME fn` >>
  Cases_on `fn_entry_label fn` >> simp[dftGasFromListTraceDefsTheory.trace_function_def,
    dftGasToListTraceTheory.trace_function_def, trace_events_def] >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  mp_tac (Q.INST [`p` |-> `[]`, `d` |-> `0`, `C` |-> `C`, `fn` |-> `fn`,
    `u` |-> `v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`]
    native_blocks_oracle_agreement) >>
  simp[]
QED

Theorem request_cut_native_event_visit:
  trace_agrees orc (dftGasFromListTraceDefs$trace_context fuel C
    (v with vs_gas_readings := readings)) /\
  MEM (n,p,d,fn,inst,t) (trace_visits 0 (dftGasToListTrace$trace_context orc fuel C v)) ==>
  ?ws. raw_reachable (v with vs_gas_readings := readings) C fn inst
    (t with vs_gas_readings := ws)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule native_context_oracle_agreement >> strip_tac >>
  drule_all replay_context_visit >> metis_tac[]
QED

Theorem request_cut_terminal_native_event_cover:
  EVERY wf_function C.ctx_functions /\
  v' = (v with vs_gas_readings := rds) /\
  terminates (run_context bound C v') /\
  trace_agrees orc (dftGasFromListTraceDefs$trace_context bound C v') /\
  ev_reachable orc v C p d fn inst t ==>
  ?ws. raw_reachable v' C fn inst (t with vs_gas_readings := ws)
Proof
  strip_tac >> drule_all ev_reachable_trace_witness >> strip_tac >>
  `!e. ev_context orc bound C v <> Error e` by
    (`restore_rel v.vs_gas_readings (run_context bound C v') (ev_context orc bound C v)` by
      (drule dftGasFromListReplayTheory.trace_context_replay >>
       disch_then (qspec_then `v.vs_gas_readings` mp_tac) >> fs[]) >>
     Cases_on `run_context bound C v'` >> Cases_on `ev_context orc bound C v` >>
     fs[restore_rel_cases, terminates_def]) >>
  `bound <= MAX bound fuel /\ fuel <= MAX bound fuel` by simp[] >>
  `dftGasToListTrace$trace_context orc (MAX bound fuel) C v =
    dftGasToListTrace$trace_context orc bound C v` by
    (mp_tac (Q.INST [`fuel` |-> `bound`, `larger` |-> `MAX bound fuel`,
       `ctx` |-> `C`, `orc` |-> `orc`, `s` |-> `v`] trace_context_fuel_extension) >>
     simp[trace_extension_def]) >>
  `MEM (n,p,d,fn,inst,t)
    (trace_visits 0 (dftGasToListTrace$trace_context orc bound C v))` by
    metis_tac[context_visits_fuel_preserved] >>
  metis_tac[request_cut_native_event_visit]
QED

Theorem native_trace_key_agreement[local]:
  agrees orc ws (trace_events (dftGasToListTrace$trace_blocks orc p d fuel C fn s)) ==>
  trace_agrees orc (dftGasFromListTraceDefs$trace_blocks p d fuel C fn
    (s with vs_gas_readings := ws))
Proof
  strip_tac >>
  qabbrev_tac `rows = dftGasFromListTraceDefs$trace_blocks p d fuel C fn
    (s with vs_gas_readings := ws)` >>
  `MAP FST (trace_gas rows) =
    trace_events (dftGasToListTrace$trace_blocks orc p d fuel C fn s)` by
    (simp[Abbr `rows`] >> irule (cj 3 oracle_native_trace_keys) >> simp[]) >>
  `MAP SND (trace_gas rows) = gas_prefix (LENGTH (trace_gas rows)) ws` by
    simp[Abbr `rows`, cj 3 trace_gas_readings, cj 3 trace_gas_lengths] >>
  fs[trace_agrees_def, EVERY_EL, agrees_def, EL_MAP] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
  rename1 `n < LENGTH (trace_gas rows)` >>
  Cases_on `EL n (trace_gas rows)` >> simp[] >>
  qpat_assum `MAP SND (trace_gas rows) = _`
    (mp_tac o Q.AP_TERM `EL n`) >>
  `LENGTH (trace_events (dftGasToListTrace$trace_blocks orc p d fuel C fn s)) =
    LENGTH (trace_gas rows)` by metis_tac[LENGTH_MAP] >>
  qpat_assum `MAP FST (trace_gas rows) = _`
    (mp_tac o Q.AP_TERM `EL n`) >>
  simp[EL_MAP, gas_prefix_genlist, EL_GENLIST, padded_reading_def]
QED

Theorem native_context_trace_items[local]:
  trace_agrees orc (dftGasFromListTraceDefs$trace_context fuel C
       (s with vs_gas_readings := ws)) ==>
  dftGasToListTrace$trace_context orc fuel C s =
    ^nativeTraceItems s.vs_gas_readings
      (dftGasFromListTraceDefs$trace_context fuel C (s with vs_gas_readings := ws))
Proof
  Cases_on `C.ctx_entry` >> simp[dftGasFromListTraceDefsTheory.trace_context_def,
    dftGasToListTraceTheory.trace_context_def] >>
  rename1 `C.ctx_entry = SOME name` >>
  Cases_on `lookup_function name C.ctx_functions` >>
  simp[dftGasFromListTraceDefsTheory.trace_function_def,
       dftGasToListTraceTheory.trace_function_def] >>
  rename1 `lookup_function name C.ctx_functions = SOME fn` >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  qspecl_then [`[]`, `0`, `fuel`, `C`, `fn`,
    `s with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0;
        vs_gas_readings := ws|>`, `orc`, `s.vs_gas_readings`]
    mp_tac (cj 3 request_cut_native_event_trace) >> simp[]
QED

Theorem native_trace_context_key_agreement[local]:
  agrees orc ws (trace_events (dftGasToListTrace$trace_context orc fuel C s)) ==>
  trace_agrees orc (dftGasFromListTraceDefs$trace_context fuel C
    (s with vs_gas_readings := ws))
Proof
  Cases_on `C.ctx_entry` >> simp[dftGasFromListTraceDefsTheory.trace_context_def,
    dftGasToListTraceTheory.trace_context_def, trace_agrees_def, trace_gas_nil] >>
  rename1 `C.ctx_entry = SOME name` >>
  Cases_on `lookup_function name C.ctx_functions` >>
  simp[dftGasFromListTraceDefsTheory.trace_function_def,
       dftGasToListTraceTheory.trace_function_def] >>
  rename1 `lookup_function name C.ctx_functions = SOME fn` >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  mp_tac (Q.INST [`p` |-> `[]`, `d` |-> `0`, `s` |->
   `s with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`]
   native_trace_key_agreement) >>
  simp[trace_agrees_def]
QED

Theorem native_trace_ids[local]:
  (!p d fuel C fn i s.
    EVERY (\((p,d,id),fn,i,s). id = i.inst_id)
      (dftGasFromListTraceDefs$trace_step p d fuel C fn i s)) /\
  (!p d fuel C fn bb s.
    EVERY (\((p,d,id),fn,i,s). id = i.inst_id)
      (dftGasFromListTraceDefs$trace_block p d fuel C fn bb s)) /\
  (!p d fuel C fn s.
    EVERY (\((p,d,id),fn,i,s). id = i.inst_id)
      (dftGasFromListTraceDefs$trace_blocks p d fuel C fn s))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume native_trace_ids[step]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[cj 1 trace_defs] >>
  Cases_on `i.inst_opcode = INVOKE` >> simp[] >>
  Cases_on `decode_invoke i` >> simp[] >>
  rename1 `decode_invoke i = SOME decoded` >> PairCases_on `decoded` >>
  Cases_on `lookup_function decoded0 C.ctx_functions` >> simp[] >>
  Cases_on `eval_operands decoded1 s` >> simp[] >>
  rename1 `eval_operands decoded1 s = SOME args` >>
  rename1 `lookup_function decoded0 C.ctx_functions = SOME callee` >>
  Cases_on `setup_callee callee args s` >> simp[] >> metis_tac[]
QED

Resume native_trace_ids[block]:
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[cj 2 trace_defs] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `step_inst fuel C inst s` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >> metis_tac[]
QED

Resume native_trace_ids[blocks]:
  rpt gen_tac >> strip_tac >>
  namedCases_on `fuel` ["", "f"] >> simp[Once (cj 3 trace_defs)] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> simp[] >>
  rename1 `eval_phis s bb.bb_instructions = OK s'` >>
  Cases_on `run_block_non_phis f C bb (s' with vs_inst_idx :=
    phi_prefix_length bb.bb_instructions)` >> simp[] >>
  rename1 `run_block_non_phis _ _ _ _ = OK u` >>
  Cases_on `u.vs_halted` >> simp[] >> metis_tac[]
QED

Finalise native_trace_ids

Theorem native_context_trace_ids[local]:
  EVERY (\((p,d,id),fn,i,s). id = i.inst_id)
    (dftGasFromListTraceDefs$trace_context fuel C s)
Proof
  Cases_on `C.ctx_entry` >> simp[dftGasFromListTraceDefsTheory.trace_context_def] >>
  rename1 `C.ctx_entry = SOME name` >>
  Cases_on `lookup_function name C.ctx_functions` >>
  simp[dftGasFromListTraceDefsTheory.trace_function_def] >>
  rename1 `lookup_function name C.ctx_functions = SOME fn` >>
  Cases_on `fn_entry_label fn` >> simp[cj 3 native_trace_ids]
QED

Theorem native_trace_visit_member[local]:
  !rows ws p d fn inst s.
  EVERY (\((p,d,id),fn,i,s). id = i.inst_id) rows /\
  MEM (TraceVisit p d fn inst s) (^nativeTraceItems ws rows) ==>
  ?t. MEM ((p,d,inst.inst_id),fn,inst,t) rows /\ s = (t with vs_gas_readings := ws)
Proof
  BETA_TAC >> Induct >> simp[] >>
  gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> Cases_on `h4.inst_opcode = GAS` >>
  simp[MEM_APPEND] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem trace_context_item_mono[local]:
  fuel <= larger /\ MEM x (dftGasToListTrace$trace_context orc fuel C s) ==>
  MEM x (dftGasToListTrace$trace_context orc larger C s)
Proof
  strip_tac >>
  mp_tac (Q.INST [`ctx` |-> `C`] trace_context_fuel_extension) >>
  simp[trace_extension_def] >> strip_tac >> simp[MEM_APPEND]
QED

(* Joint DFT cursor replay and the normalized request proof may produce
   their witnesses independently. The event key determines the visit. *)
Theorem request_cut_event_visit_unique:
  EVERY wf_function C.ctx_functions /\
  EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    f.fn_blocks) C.ctx_functions /\
  ev_reachable orc initial C p d fn i s /\
  ev_reachable orc initial C p d fn' i' s' /\ i.inst_id = i'.inst_id ==>
  fn = fn' /\ i = i' /\ s = s'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `ev_reachable orc initial C p d fn i s`
    (mp_tac o MATCH_MP ev_reachable_trace_item) >>
  simp[] >> disch_then (qx_choose_then `n` assume_tac) >>
  qpat_assum `ev_reachable orc initial C p d fn' i' s'`
    (mp_tac o MATCH_MP ev_reachable_trace_item) >>
  simp[] >> disch_then (qx_choose_then `m` assume_tac) >>
  qabbrev_tac `rows = dftGasToListTrace$trace_context orc (MAX n m) C initial` >>
  `n <= MAX n m /\ m <= MAX n m` by simp[] >>
  `MEM (TraceVisit p d fn i s) rows /\ MEM (TraceVisit p d fn' i' s') rows` by
    (simp[Abbr `rows`] >> conj_tac
     >- (irule trace_context_item_mono >> qexists_tac `n` >> simp[]) >>
     irule trace_context_item_mono >> qexists_tac `m` >> simp[]) >>
  qabbrev_tac `ws = MAP orc (trace_events rows)` >>
  qabbrev_tac `vs = initial with vs_gas_readings := ws` >>
  qabbrev_tac `native = dftGasFromListTraceDefs$trace_context (MAX n m) C vs` >>
  `trace_agrees orc native` by
    (simp[Abbr `native`, Abbr `vs`] >>
     irule native_trace_context_key_agreement >> simp[Abbr `ws`, Abbr `rows`, agrees_map]) >>
  `rows = ^nativeTraceItems initial.vs_gas_readings native` by
    (simp[Abbr `rows`, Abbr `native`, Abbr `vs`] >>
     irule (BETA_RULE native_context_trace_items) >> metis_tac[]) >>
  `EVERY (\((p,d,id),fn,i,s). id = i.inst_id) native /\
   ALL_DISTINCT (MAP FST native)` by
    simp[Abbr `native`, native_context_trace_ids, trace_context_names_distinct] >>
  `?t. MEM ((p,d,i.inst_id),fn,i,t) native /\ s = (t with vs_gas_readings := initial.vs_gas_readings)` by
    metis_tac[BETA_RULE native_trace_visit_member] >>
  `?t'. MEM ((p,d,i'.inst_id),fn',i',t') native /\ s' = (t' with vs_gas_readings := initial.vs_gas_readings)` by
    metis_tac[BETA_RULE native_trace_visit_member] >>
  `((p,d,i.inst_id),fn,i,t) = ((p,d,i'.inst_id),fn',i',t')` by
    (qspecl_then [`FST : list_visit -> ((num # num) list # num # num)`, `native`,
       `((p,d,i.inst_id),fn,i,t)`, `((p,d,i'.inst_id),fn',i',t')`] mp_tac
       dftCorrectnessTheory.all_distinct_map_mem_inj >> simp[]) >>
  gvs[]
QED

Theorem request_cut_native_trace_reachable:
  EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    f.fn_blocks) C.ctx_functions /\
  dftGasFromListTraceDefs$trace_context fuel C v = pre ++ ((p,d,id),fn,inst,s)::after ==>
  raw_reachable v C fn inst s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule finite_trace_oracle >> disch_then (qspec_then `v` strip_assume_tac) >>
  `v with vs_gas_readings := v.vs_gas_readings = v` by
    simp[venom_state_component_equality] >>
  `agrees orc v.vs_gas_readings (trace_events
    (dftGasToListTrace$trace_context orc fuel C v))` by
    (mp_tac (Q.INST [`C` |-> `C`, `u` |-> `v`, `v` |-> `v`,
        `rds` |-> `v.vs_gas_readings`] native_context_oracle_agreement) >>
     PURE_ASM_REWRITE_TAC [] >>
     qpat_assum `!n. trace_agrees _ _` (qspec_then `fuel` mp_tac) >>
     PURE_ASM_REWRITE_TAC [] >> metis_tac[]) >>
  `dftGasToListTrace$trace_context orc fuel C v =
     ^nativeTraceItems v.vs_gas_readings (pre ++ ((p,d,id),fn,inst,s)::after)` by
    (mp_tac (Q.INST [`ws` |-> `v.vs_gas_readings`, `s` |-> `v`]
       native_context_trace_items) >>
     PURE_ASM_REWRITE_TAC [] >>
     qpat_assum `!n. trace_agrees _ _` (qspec_then `fuel` mp_tac) >>
     PURE_ASM_REWRITE_TAC [] >> metis_tac[]) >>
  `MEM (LENGTH (trace_gas pre),p,d,fn,inst,s with vs_gas_readings := v.vs_gas_readings)
    (trace_visits 0 (dftGasToListTrace$trace_context orc fuel C v))` by
    simp[MAP_APPEND, FLAT_APPEND, trace_visits_append, BETA_RULE native_event_trace_gas_keys,
         trace_visits_def] >>
  `s.vs_gas_readings = DROP (LENGTH (trace_gas pre)) v.vs_gas_readings` by
    (qpat_x_assum `dftGasFromListTraceDefs$trace_context fuel C v = _` mp_tac >>
     Cases_on `C.ctx_entry` >> simp[dftGasFromListTraceDefsTheory.trace_context_def] >>
     rename1 `C.ctx_entry = SOME nm` >>
     Cases_on `lookup_function nm C.ctx_functions` >> simp[] >>
     rename1 `lookup_function nm C.ctx_functions = SOME entry` >>
     Cases_on `fn_entry_label entry` >> simp[dftGasFromListTraceDefsTheory.trace_function_def] >>
     rename1 `fn_entry_label entry = SOME lbl` >>
     qabbrev_tac `v' = v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` >>
     disch_tac >>
     qspecl_then [`[]`, `0`, `fuel`, `C`, `entry`, `v'`, `LENGTH pre`]
       mp_tac (cj 3 trace_visit_readings) >>
     PURE_ASM_REWRITE_TAC [] >>
     simp[EL_APPEND_EQN, listTheory.TAKE_APPEND1, Abbr `v'`]) >>
  `s with vs_gas_readings := DROP (LENGTH (trace_gas pre)) v.vs_gas_readings = s` by
    simp[venom_state_component_equality] >>
  drule_all replay_context_visit >>
  disch_then (mp_tac o SIMP_RULE (srw_ss()) []) >>
  PURE_ASM_REWRITE_TAC [] >> simp[]
QED

(* Finite event logs have a native realization at the same fuel. *)
Theorem request_cut_canonical_native_trace:
  ?readings.
    dftGasToListTrace$trace_context orc fuel C v =
    ^nativeTraceItems v.vs_gas_readings
      (dftGasFromListTraceDefs$trace_context fuel C (v with vs_gas_readings := readings))
Proof
  qexists_tac `MAP orc (trace_events (dftGasToListTrace$trace_context orc fuel C v))` >>
  BETA_TAC >>
  irule (BETA_RULE native_context_trace_items) >>
  irule native_trace_context_key_agreement >> simp[agrees_map]
QED
