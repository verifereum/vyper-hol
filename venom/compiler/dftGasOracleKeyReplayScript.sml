Theory dftGasOracleKeyReplay
Ancestors
  dftGasToListReplay dftGasToListAgreement dftGasToListTrace
  dftGasFromListTraceDefs dftGasFromListReadings
  dftGasInvResidualTrace
  dftGasOracleDefs gasOracleReplay contextCodegenRel
  stateEquiv venomExecProofs venomExecSemantics venomState venomInst list rich_list arithmetic

(* Key projection follows the actual oracle run, including stopped children. *)
Theorem oracle_native_trace_keys:
  (!orc p d fuel ctx inst s. !ws fn.
    agrees orc ws (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s)) ==>
    MAP FST (visit_gas ((p,d,inst.inst_id),fn,inst,s with vs_gas_readings := ws) ++
      trace_gas (dftGasFromListTraceDefs$trace_step p d fuel ctx fn inst
        (s with vs_gas_readings := ws))) =
    trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s)) /\
  (!orc p d fuel ctx fn bb s. !ws.
    agrees orc ws (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s)) ==>
    MAP FST (trace_gas (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb
      (s with vs_gas_readings := ws))) =
    trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s)) /\
  (!orc p d fuel ctx fn s. !ws.
    agrees orc ws (trace_events (dftGasToListTrace$trace_blocks orc p d fuel ctx fn s)) ==>
    MAP FST (trace_gas (dftGasFromListTraceDefs$trace_blocks p d fuel ctx fn
      (s with vs_gas_readings := ws))) =
    trace_events (dftGasToListTrace$trace_blocks orc p d fuel ctx fn s))
Proof
  ho_match_mp_tac oracle_trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume oracle_native_trace_keys[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  simp[trace_step_eq, Once dftGasFromListTraceDefsTheory.trace_defs,
       visit_gas_def, trace_events_def] >>
  Cases_on `inst.inst_opcode = GAS` >> simp[trace_events_def]
QED

Resume oracle_native_trace_keys[invoke]:
  simp[trace_step_eq, Once dftGasFromListTraceDefsTheory.trace_defs,
       visit_gas_def, gas_eval_operands, gas_setup_callee, trace_events_def] >>
  Cases_on `decode_invoke inst` >> simp[trace_events_def] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[trace_events_def] >>
  rename1 `lookup_function pair0 ctx.ctx_functions = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> simp[trace_events_def] >>
  rename1 `eval_operands pair1 s = SOME args` >>
  Cases_on `setup_callee callee args s` >> simp[trace_events_def] >>
  rename1 `setup_callee callee args s = SOME cs` >>
  simp[gas_setup_callee] >> metis_tac[]
QED

Resume oracle_native_trace_keys[block]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[trace_block_eq, dftGasFromListTraceDefsTheory.trace_defs] >> simp[] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[trace_gas_def, trace_events_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  simp[trace_gas_cons, trace_gas_append, MAP_APPEND, trace_events_def,
       trace_events_append] >> strip_tac >>
  `agrees orc ws (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s))` by
    (fs[trace_events_append, agrees_append]) >>
  `MAP FST (visit_gas ((p,d,inst.inst_id),fn,inst,s with vs_gas_readings := ws) ++
      trace_gas (dftGasFromListTraceDefs$trace_step p d fuel ctx fn inst
        (s with vs_gas_readings := ws))) =
    trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s)` by
    metis_tac[] >>
  `residual_result
      (DROP (LENGTH (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s))) ws)
      (ev_step orc p d fuel ctx inst s)
      (step_inst fuel ctx inst (s with vs_gas_readings := ws))` by
    metis_tac[cj 1 dftGasToListReplayTheory.trace_replay] >>
  Cases_on `ev_step orc p d fuel ctx inst s` >>
  Cases_on `step_inst fuel ctx inst (s with vs_gas_readings := ws)` >>
  gvs[residual_result_def, lift_result_def, MAP_APPEND, trace_events_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[trace_events_def, agrees_append] >>
  metis_tac[]
QED

Resume oracle_native_trace_keys[blocks]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `fuel`
  >- simp[dftGasFromListTraceDefsTheory.trace_blocks_zero,
           dftGasToListTraceTheory.trace_blocks_zero, trace_gas_def, trace_events_def] >>
  rename1 `SUC k` >>
  once_rewrite_tac[dftGasToListTraceTheory.trace_blocks_eq,
                   dftGasFromListTraceDefsTheory.trace_defs] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[trace_gas_def, trace_events_def] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  qspecl_then [`bb.bb_instructions`, `s`, `ws`] mp_tac replay_phis >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  Cases_on `eval_phis (s with vs_gas_readings := ws) bb.bb_instructions` >>
  gvs[residual_result_def, lift_result_def, trace_events_def] >> strip_tac >>
  gvs[trace_events_def] >>
  simp[trace_gas_append, MAP_APPEND, trace_events_append, agrees_append] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `ev_block orc p (SUC d) k ctx bb entry` >>
  `residual_result
      (DROP (LENGTH (trace_events (dftGasToListTrace$trace_block orc p (SUC d) k ctx fn bb entry))) ws)
      (ev_block orc p (SUC d) k ctx bb entry)
      (exec_block k ctx bb (entry with vs_gas_readings := ws))` by
    (irule (cj 2 dftGasToListReplayTheory.trace_replay) >> simp[Abbr `entry`]) >>
  Cases_on `ev_block orc p (SUC d) k ctx bb entry` >>
  Cases_on `exec_block k ctx bb (entry with vs_gas_readings := ws)` >>
  gvs[residual_result_def, lift_result_def, trace_gas_append, MAP_APPEND,
      trace_events_def, trace_events_append, agrees_append, Abbr `entry`] >>
  rename1 `ev_block orc p (SUC d) k ctx bb _ = OK out` >>
  Cases_on `out.vs_halted` >> gvs[trace_events_def] >> metis_tac[]
QED

Finalise oracle_native_trace_keys

(* Retained child rows cover a stopped call; completed calls consume their row. *)
Theorem oracle_prefix_key_rows:
  !pre kss s bb.
    DROP s.vs_inst_idx bb.bb_instructions = pre /\
    LIST_REL (\i keys.
      if i.inst_opcode = GAS then keys = [(p,d,i.inst_id)]
      else if i.inst_opcode = INVOKE then T else keys = []) pre kss /\
    (!j st.
      j < LENGTH pre /\ (EL j pre).inst_opcode = INVOKE /\
      inv_ev_trace orc p d fuel ctx (TAKE j pre) s st ==>
      (?extra. EL j kss =
        trace_events (dftGasToListTrace$trace_step orc p d fuel ctx (EL j pre) st) ++ extra) /\
      (!u. ev_step orc p d fuel ctx (EL j pre) st = OK u ==>
        trace_events (dftGasToListTrace$trace_step orc p d fuel ctx (EL j pre) st) = EL j kss)) ==>
    (?extra. FLAT kss =
      trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s) ++ extra) /\
    (!t. inv_ev_trace orc p d fuel ctx pre s t ==>
      trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s) = FLAT kss)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[DROP_EQ_NIL] >>
      once_rewrite_tac[trace_block_eq] >>
      simp[get_instruction_def, trace_events_def]) >>
  namedCases_on `kss` ["", "row rows"] >> gvs[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _::_`
      (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  `(?extra. row =
      trace_events (dftGasToListTrace$trace_step orc p d fuel ctx h s) ++ extra) /\
   (!u. ev_step orc p d fuel ctx h s = OK u ==>
      trace_events (dftGasToListTrace$trace_step orc p d fuel ctx h s) = row)` by
    (Cases_on `h.inst_opcode = INVOKE`
     >- (qpat_x_assum `!j st. _ /\ _ /\ inv_ev_trace _ _ _ _ _ _ _ _ ==> _`
           (qspecl_then [`0`, `s`] mp_tac) >> simp[inv_ev_trace_def]) >>
     Cases_on `h.inst_opcode = GAS` >> gvs[trace_step_eq, trace_events_def]) >>
  Cases_on `ev_step orc p d fuel ctx h s`
  >- suspend "row_ok"
  >> (once_rewrite_tac[trace_block_eq] >>
      simp[get_instruction_def, trace_events_def,
           trace_events_append, inv_ev_trace_def] >>
      metis_tac[APPEND_ASSOC])
QED

Resume oracle_prefix_key_rows[row_ok]:
  rename1 `ev_step orc p d fuel ctx h s = OK out` >>
  `row = trace_events (dftGasToListTrace$trace_step orc p d fuel ctx h s)` by
    metis_tac[] >>
  qpat_x_assum `!u. _ = OK u ==> _` kall_tac >>
  qpat_x_assum `row = _ ++ _` kall_tac >>
  Cases_on `is_terminator h.inst_opcode`
  >- (qpat_x_assum `!j st. _ /\ _ /\ inv_ev_trace _ _ _ _ _ _ _ _ ==> _` kall_tac >>
      once_rewrite_tac[trace_block_eq] >>
      simp[get_instruction_def, trace_events_def, trace_events_append, inv_ev_trace_def] >>
      metis_tac[APPEND_ASSOC]) >>
  `(!j st.
      j < LENGTH pre /\ (EL j pre).inst_opcode = INVOKE /\
      inv_ev_trace orc p d fuel ctx (TAKE j pre)
        (out with vs_inst_idx := SUC s.vs_inst_idx) st ==>
      (?extra. EL j rows =
        trace_events (dftGasToListTrace$trace_step orc p d fuel ctx (EL j pre) st) ++ extra) /\
      (!u. ev_step orc p d fuel ctx (EL j pre) st = OK u ==>
        trace_events (dftGasToListTrace$trace_step orc p d fuel ctx (EL j pre) st) = EL j rows))` by
    (rpt strip_tac >>
     qpat_x_assum `!j st. _ /\ _ /\ inv_ev_trace _ _ _ _ _ _ _ _ ==> _`
       (qspecl_then [`SUC j`, `st`] mp_tac) >>
     simp[inv_ev_trace_def] >> metis_tac[]) >>
  qpat_x_assum `!kss s bb. _`
    (qspecl_then [`rows`, `out with vs_inst_idx := SUC s.vs_inst_idx`, `bb`] mp_tac) >>
  impl_tac >- (simp[NoAsms] >> metis_tac[]) >> strip_tac >>
  qpat_x_assum `!j st. _ /\ _ /\ inv_ev_trace _ _ _ _ _ _ _ _ ==> _` kall_tac >>
  qpat_x_assum `!j st. _ /\ _ /\ inv_ev_trace _ _ _ _ _ _ _ _ ==> _` kall_tac >>
  conj_tac
  >- (once_rewrite_tac[trace_block_eq] >>
      simp[get_instruction_def, trace_events_def, trace_events_append] >>
      metis_tac[APPEND_ASSOC]) >>
  qpat_x_assum `FLAT rows = _ ++ _` kall_tac >>
  once_rewrite_tac[trace_block_eq] >>
  simp[get_instruction_def, trace_events_def,
       trace_events_append, inv_ev_trace_def] >> metis_tac[APPEND_ASSOC]
QED

Finalise oracle_prefix_key_rows

Theorem oracle_block_trace_packet:
  agrees orc (gs ++ tail)
    (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s)) /\
  LENGTH gs = LENGTH
    (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s)) ==>
  trace_gas (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb
    (s with vs_gas_readings := gs ++ tail)) =
    ZIP (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s),gs) /\
  residual_result tail (ev_block orc p d fuel ctx bb s)
    (exec_block fuel ctx bb (s with vs_gas_readings := gs ++ tail))
Proof
  strip_tac >>
  `MAP FST (trace_gas (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb
      (s with vs_gas_readings := gs ++ tail))) =
    trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s)` by
    (irule (cj 2 oracle_native_trace_keys) >> simp[]) >>
  `LENGTH (trace_gas (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb
      (s with vs_gas_readings := gs ++ tail))) = LENGTH gs` by metis_tac[LENGTH_MAP] >>
  `gas_count_block fuel ctx bb (s with vs_gas_readings := gs ++ tail) = LENGTH gs` by
    metis_tac[cj 2 trace_gas_lengths] >>
  `MAP SND (trace_gas (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb
      (s with vs_gas_readings := gs ++ tail))) = gs` by
    (mp_tac (cj 2 trace_gas_readings) >>
     disch_then (qspecl_then [`p`, `d`, `fuel`, `ctx`, `fn`, `bb`,
       `s with vs_gas_readings := gs ++ tail`] mp_tac) >>
     simp[NoAsms,
       ASSUME ``gas_count_block fuel ctx bb (s with vs_gas_readings := gs ++ tail) = LENGTH gs``,
       gas_prefix_def, TAKE_APPEND]) >>
  conj_tac
  >- metis_tac[ZIP_UNZIP, UNZIP_MAP] >>
  `DROP (LENGTH (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s)))
    (gs ++ tail) = tail` by metis_tac[DROP_LENGTH_APPEND] >>
  mp_tac (cj 2 dftGasToListReplayTheory.trace_replay) >>
  disch_then (qspecl_then [`orc`, `p`, `d`, `fuel`, `ctx`, `fn`, `bb`, `s`, `gs ++ tail`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  metis_tac[]
QED

Theorem oracle_prefix_replay:
  !pre s t bb ws.
    DROP s.vs_inst_idx bb.bb_instructions = pre /\
    inv_ev_trace orc p d fuel ctx pre s t /\
    agrees orc ws
      (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s)) ==>
    FOLDR (dft_exec_cons fuel ctx) OK pre (s with vs_gas_readings := ws) =
    OK (t with vs_gas_readings := DROP
      (LENGTH (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s))) ws)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[inv_ev_trace_def, DROP_EQ_NIL] >>
      once_rewrite_tac[trace_block_eq] >>
      simp[get_instruction_def, trace_events_def]) >>
  fs[inv_ev_trace_def] >>
  rename1 `ev_step orc p d fuel ctx h s = OK out` >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _::_`
      (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  `trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s) =
    trace_events (dftGasToListTrace$trace_step orc p d fuel ctx h s) ++
    trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb
      (out with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[Once trace_block_eq, get_instruction_def, trace_events_def,
          trace_events_append]) >>
  fs[agrees_append] >>
  `step_inst fuel ctx h (s with vs_gas_readings := ws) =
    OK (out with vs_gas_readings := DROP
      (LENGTH (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx h s))) ws)` by
    (mp_tac (cj 1 dftGasToListReplayTheory.trace_replay) >>
     disch_then (qspecl_then [`orc`, `p`, `d`, `fuel`, `ctx`, `h`, `s`, `ws`] mp_tac) >>
     simp[]) >>
  qpat_x_assum `!s t bb ws. _`
    (qspecl_then [`out with vs_inst_idx := SUC s.vs_inst_idx`, `t`, `bb`,
      `DROP (LENGTH (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx h s))) ws`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[dftIndexedExecTheory.dft_exec_cons_def, DROP_DROP_T, ADD_COMM]
QED

Theorem fixed_key_rows_native_replay:
  !pre kss s bb gs tail.
    DROP s.vs_inst_idx bb.bb_instructions = pre /\
    LIST_REL (\i keys.
      if i.inst_opcode = GAS then keys = [(p,d,i.inst_id)]
      else if i.inst_opcode = INVOKE then T else keys = []) pre kss /\
    (!j st.
      j < LENGTH pre /\ (EL j pre).inst_opcode = INVOKE /\
      inv_ev_trace orc p d fuel ctx (TAKE j pre) s st ==>
      (?extra. EL j kss =
        trace_events (dftGasToListTrace$trace_step orc p d fuel ctx (EL j pre) st) ++ extra) /\
      (!u. ev_step orc p d fuel ctx (EL j pre) st = OK u ==>
        trace_events (dftGasToListTrace$trace_step orc p d fuel ctx (EL j pre) st) = EL j kss)) /\
    agrees orc (gs ++ tail) (FLAT kss) /\ LENGTH gs = LENGTH (FLAT kss) ==>
    (?extra. FLAT kss = MAP FST (trace_gas
      (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb
        (s with vs_gas_readings := gs ++ tail))) ++ extra) /\
    (!t. inv_ev_trace orc p d fuel ctx pre s t ==>
      FOLDR (dft_exec_cons fuel ctx) OK pre (s with vs_gas_readings := gs ++ tail) =
        OK (t with vs_gas_readings := tail) /\
      trace_gas (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb
        (s with vs_gas_readings := gs ++ tail)) = ZIP (FLAT kss,gs))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac oracle_prefix_key_rows >>
  disch_then (qspecl_then [`pre`, `kss`, `s`, `bb`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  `agrees orc (gs ++ tail)
    (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s))` by
    (qpat_x_assum `agrees _ _ (FLAT kss)` mp_tac >>
     simp[agrees_append]) >>
  `MAP FST (trace_gas (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb
      (s with vs_gas_readings := gs ++ tail))) =
    trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s)` by
    (irule (cj 2 oracle_native_trace_keys) >> asm_rewrite_tac[]) >>
  conj_tac >- metis_tac[] >> gen_tac >> strip_tac >>
  `trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s) = FLAT kss` by
    metis_tac[] >>
  `LENGTH gs = LENGTH
    (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s))` by metis_tac[] >>
  `DROP (LENGTH (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s)))
    (gs ++ tail) = tail` by metis_tac[DROP_LENGTH_APPEND] >>
  conj_tac
  >- (mp_tac oracle_prefix_replay >>
      disch_then (qspecl_then [`pre`, `s`, `t`, `bb`, `gs ++ tail`] mp_tac) >>
      impl_tac >- metis_tac[] >> metis_tac[]) >>
  drule_all oracle_block_trace_packet >> metis_tac[]
QED
