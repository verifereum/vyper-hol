Theory dftPacketNativeSupplierReplay
Ancestors
  dftGasOracleKeyReplay dftGasFromListReplay dftGasPrefixProvider
  dftGasToListAgreement dftGasToListReplay dftGasToListTrace
  dftGasFromListRestore dftGasFromListTraceDefs dftGasOracleDefs
  dftGasFromListReadings dftGasInvResidualTrace dftIndexedExec
  gasOracleReplay gasCount venomExecSemantics venomState venomInst
  list rich_list arithmetic

Theorem key_readings_agree[local]:
  MAP SND events = gas_prefix (LENGTH events) ws /\
  agrees orc ws (MAP FST events) ==>
  EVERY (\(e,w). orc e = w) events
Proof
  simp[EVERY_EL, agrees_def, gas_prefix_genlist, LIST_EQ_REWRITE] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >>
  qpat_x_assum `!i. _ ==> _` (qspec_then `n` mp_tac) >>
  simp[EL_MAP, EL_GENLIST, padded_reading_def] >>
  Cases_on `EL n events` >> simp[]
QED

Theorem native_row_supplier_replay[local]:
  (?extra. keys = MAP FST
    (visit_gas ((p,d,i.inst_id),fn,i,s with vs_gas_readings := gs ++ tail) ++
     trace_gas (dftGasFromListTraceDefs$trace_step p d fuel C fn i
       (s with vs_gas_readings := gs ++ tail))) ++ extra) /\
  (!u. step_inst fuel C i (s with vs_gas_readings := gs ++ tail) = OK u ==>
    MAP FST
      (visit_gas ((p,d,i.inst_id),fn,i,s with vs_gas_readings := gs ++ tail) ++
       trace_gas (dftGasFromListTraceDefs$trace_step p d fuel C fn i
         (s with vs_gas_readings := gs ++ tail))) = keys) /\
  LENGTH keys = LENGTH gs /\ agrees orc (gs ++ tail) keys /\
  ev_step orc p d fuel C i s = OK t ==>
  step_inst fuel C i (s with vs_gas_readings := gs ++ tail) =
    OK (t with vs_gas_readings := tail) /\
  visit_gas ((p,d,i.inst_id),fn,i,s with vs_gas_readings := gs ++ tail) ++
    trace_gas (dftGasFromListTraceDefs$trace_step p d fuel C fn i
      (s with vs_gas_readings := gs ++ tail)) = ZIP (keys,gs)
Proof
  strip_tac >>
  `trace_agrees orc
    (((p,d,i.inst_id),fn,i,s with vs_gas_readings := gs ++ tail)::
      dftGasFromListTraceDefs$trace_step p d fuel C fn i
        (s with vs_gas_readings := gs ++ tail))` by
    (pure_rewrite_tac[trace_agrees_def, trace_gas_cons] >>
     irule key_readings_agree >> qexists_tac `gs ++ tail` >> conj_tac
     >- simp[cj 1 trace_gas_readings, cj 1 trace_gas_lengths] >>
     gvs[agrees_append]) >>
  `restore_rel s.vs_gas_readings
     (step_inst fuel C i (s with vs_gas_readings := gs ++ tail))
     (ev_step orc p d fuel C i s)` by
    (mp_tac (cj 1 dftGasFromListReplayTheory.trace_replay) >>
     disch_then (qspecl_then [`p`, `d`, `fuel`, `C`, `fn`, `i`,
       `s with vs_gas_readings := gs ++ tail`, `orc`, `s.vs_gas_readings`] mp_tac) >>
     simp[]) >>
  `?v. step_inst fuel C i (s with vs_gas_readings := gs ++ tail) = OK v` by
    (Cases_on `step_inst fuel C i (s with vs_gas_readings := gs ++ tail)` >>
     fs[restore_rel_def] >> metis_tac[exec_result_distinct]) >>
  qpat_x_assum `keys = _ ++ extra` kall_tac >>
  qpat_x_assum `!u. _` drule >> strip_tac >>
  qpat_x_assum `restore_rel _ _ _` kall_tac >>
  `trace_events (dftGasToListTrace$trace_step orc p d fuel C i s) = keys` by
    (mp_tac (cj 1 native_trace_oracle_agreement) >>
     disch_then (qspecl_then [`p`, `d`, `fuel`, `C`, `fn`, `i`,
       `s with vs_gas_readings := gs ++ tail`, `orc`, `s.vs_gas_readings`] mp_tac) >>
     (gvs[])) >>
  `step_inst fuel C i (s with vs_gas_readings := gs ++ tail) =
    OK (t with vs_gas_readings := tail)` by
    (mp_tac (cj 1 dftGasToListReplayTheory.trace_replay) >>
     disch_then (qspecl_then [`orc`, `p`, `d`, `fuel`, `C`, `i`, `s`, `gs ++ tail`] mp_tac) >>
     simp[DROP_LENGTH_APPEND]) >>
  `gas_count_step fuel C i (s with vs_gas_readings := gs ++ tail) = LENGTH gs` by
    metis_tac[cj 1 trace_gas_lengths, LENGTH_MAP] >>
  simp[] >> irule LIST_EQ_MAP_PAIR >>
  pure_rewrite_tac[cj 1 trace_gas_readings] >>
  simp[MAP_ZIP, gas_prefix_def, TAKE_APPEND]
QED

Theorem dft_packet_native_supplier_replay:
  !pre kss gss s t bb tail.
    DROP s.vs_inst_idx bb.bb_instructions = pre /\
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    LIST_REL (\i keys.
      if i.inst_opcode = GAS then keys = [(p,d,i.inst_id)]
      else if i.inst_opcode = INVOKE then T else keys = []) pre kss /\
    LIST_REL (\ks gs. LENGTH ks = LENGTH gs) kss gss /\
    agrees orc (FLAT gss ++ tail) (FLAT kss) /\
    inv_ev_trace orc p d fuel C pre s t /\
    (!q u. q < LENGTH pre /\ (EL q pre).inst_opcode = INVOKE /\
      FOLDR (dft_exec_cons fuel C) OK (TAKE q pre)
        (s with vs_gas_readings := FLAT gss ++ tail) = OK u ==>
      (?extra. EL q kss = MAP FST (trace_gas
        (dftGasFromListTraceDefs$trace_step p d fuel C fn (EL q pre) u)) ++ extra) /\
      (!v. step_inst fuel C (EL q pre) u = OK v ==>
        MAP FST (trace_gas
          (dftGasFromListTraceDefs$trace_step p d fuel C fn (EL q pre) u)) = EL q kss)) ==>
    FOLDR (dft_exec_cons fuel C) OK pre
      (s with vs_gas_readings := FLAT gss ++ tail) =
        OK (t with vs_gas_readings := tail) /\
    trace_gas (dftGasFromListTraceDefs$trace_block p d fuel C fn bb
      (s with vs_gas_readings := FLAT gss ++ tail)) = ZIP (FLAT kss,FLAT gss)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[inv_ev_trace_def, DROP_EQ_NIL] >>
      simp[Once dftGasFromListTraceDefsTheory.trace_defs, get_instruction_def]) >>
  namedCases_on `kss` ["", "keys rows"] >> fs[] >>
  namedCases_on `gss` ["", "gs readings"] >> gvs[] >>
  fs[inv_ev_trace_def] >>
  rename1 `ev_step orc p d fuel C h s = OK out` >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _::_`
      (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  `agrees orc (gs ++ (FLAT readings ++ tail)) keys /\
   agrees orc (FLAT readings ++ tail) (FLAT rows)` by
    metis_tac[agrees_append, DROP_LENGTH_APPEND, APPEND_ASSOC] >>
  `(?extra. keys = MAP FST
      (visit_gas ((p,d,h.inst_id),fn,h,
         s with vs_gas_readings := gs ++ (FLAT readings ++ tail)) ++
       trace_gas (dftGasFromListTraceDefs$trace_step p d fuel C fn h
         (s with vs_gas_readings := gs ++ (FLAT readings ++ tail)))) ++ extra) /\
   (!v. step_inst fuel C h
       (s with vs_gas_readings := gs ++ (FLAT readings ++ tail)) = OK v ==>
     MAP FST
      (visit_gas ((p,d,h.inst_id),fn,h,
         s with vs_gas_readings := gs ++ (FLAT readings ++ tail)) ++
       trace_gas (dftGasFromListTraceDefs$trace_step p d fuel C fn h
         (s with vs_gas_readings := gs ++ (FLAT readings ++ tail)))) = keys)` by
    (Cases_on `h.inst_opcode = INVOKE`
     >- (qpat_x_assum `!q u. _` (qspecl_then
           [`0`, `s with vs_gas_readings := gs ++ (FLAT readings ++ tail)`] mp_tac) >>
         simp[visit_gas_def, APPEND_ASSOC]) >>
     Cases_on `h.inst_opcode = GAS` >>
     gvs[visit_gas_def, trace_step_noninvoke, AllCaseEqs()]) >>
  `step_inst fuel C h
     (s with vs_gas_readings := gs ++ (FLAT readings ++ tail)) =
       OK (out with vs_gas_readings := FLAT readings ++ tail) /\
   visit_gas ((p,d,h.inst_id),fn,h,
       s with vs_gas_readings := gs ++ (FLAT readings ++ tail)) ++
     trace_gas (dftGasFromListTraceDefs$trace_step p d fuel C fn h
       (s with vs_gas_readings := gs ++ (FLAT readings ++ tail))) = ZIP (keys,gs)` by
    (irule native_row_supplier_replay >> metis_tac[]) >>
  suspend "tail"
QED

Resume dft_packet_native_supplier_replay[tail]:
  qpat_x_assum `keys = _ ++ extra` kall_tac >>
  qpat_x_assum `!v. step_inst _ _ _ _ = OK v ==> _` kall_tac >>
  qpat_x_assum `step_inst fuel C h _ = _`
    (assume_tac o PURE_REWRITE_RULE[APPEND_ASSOC]) >>
  `!q u. q < LENGTH pre /\ (EL q pre).inst_opcode = INVOKE /\
      FOLDR (dft_exec_cons fuel C) OK (TAKE q pre)
        ((out with vs_inst_idx := SUC s.vs_inst_idx)
          with vs_gas_readings := FLAT readings ++ tail) = OK u ==>
      (?extra. EL q rows = MAP FST (trace_gas
        (dftGasFromListTraceDefs$trace_step p d fuel C fn (EL q pre) u)) ++ extra) /\
      (!v. step_inst fuel C (EL q pre) u = OK v ==>
        MAP FST (trace_gas
          (dftGasFromListTraceDefs$trace_step p d fuel C fn (EL q pre) u)) = EL q rows)` by
    (rpt strip_tac >>
     qpat_x_assum `!q u. _` (qspecl_then [`SUC q`, `u`] mp_tac) >>
     gvs[TAKE, EL, FOLDR, dft_exec_cons_def, APPEND_ASSOC]) >>
  `FOLDR (dft_exec_cons fuel C) OK pre
     ((out with vs_inst_idx := SUC s.vs_inst_idx)
       with vs_gas_readings := FLAT readings ++ tail) =
       OK (t with vs_gas_readings := tail) /\
   trace_gas (dftGasFromListTraceDefs$trace_block p d fuel C fn bb
     ((out with vs_inst_idx := SUC s.vs_inst_idx)
       with vs_gas_readings := FLAT readings ++ tail)) = ZIP (FLAT rows,FLAT readings)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  conj_tac
  >- gvs[dft_exec_cons_def, APPEND_ASSOC] >>
  simp[Once dftGasFromListTraceDefsTheory.trace_defs, get_instruction_def,
       APPEND_ASSOC, ZIP_APPEND] >>
  gvs[APPEND_ASSOC] >> irule ZIP_APPEND >> simp[] >>
  simp[LENGTH_FLAT] >> AP_TERM_TAC >>
  qpat_x_assum `LIST_REL (\ks gs. LENGTH ks = LENGTH gs) rows readings` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP]
QED

Finalise dft_packet_native_supplier_replay
