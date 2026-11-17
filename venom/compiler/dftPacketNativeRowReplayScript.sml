Theory dftPacketNativeRowReplay
Ancestors
  dftIndexedExec dftGasFromListTraceDefs dftGasFromListReadings dftGasToListReplay
  gasOracleReplay gasEvents frameGasEvents stateEquiv
  venomExecSemantics venomState venomInst list rich_list arithmetic

Theorem native_replay_list[local]:
  !pre kgss ess ks s eb tb tail.
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  DROP s.vs_inst_idx eb.bb_instructions = pre /\
  DROP s.vs_inst_idx tb.bb_instructions = pre /\
  LENGTH kgss = LENGTH pre /\ LENGTH ess = LENGTH pre /\ LENGTH ks = LENGTH pre /\
  LIST_REL (\keys ws. LENGTH keys = LENGTH ws) ks kgss /\
  (!q rest u. q < LENGTH pre /\
    FOLDR (dft_exec_cons f C) OK (TAKE q pre)
      (s with vs_gas_readings := FLAT (TAKE q kgss) ++ rest) = OK u ==>
    (!tail. ?extra. EL q ess = gas_events_step f C sf.fn_name (EL q pre)
      (u with vs_gas_readings := EL q kgss ++ tail) ++ extra) /\
    (!tail v. step_inst f C (EL q pre) (u with vs_gas_readings := EL q kgss ++ tail) = OK v ==>
      gas_events_step f C sf.fn_name (EL q pre) (u with vs_gas_readings := EL q kgss ++ tail) = EL q ess /\
      v.vs_gas_readings = tail /\
      visit_gas ((a,e,(EL q pre).inst_id),sf,EL q pre,u with vs_gas_readings := EL q kgss ++ tail) ++
        trace_gas (trace_step a e f C sf (EL q pre) (u with vs_gas_readings := EL q kgss ++ tail)) =
        ZIP (EL q ks,EL q kgss) /\
      (!tail'. step_inst f C (EL q pre) (u with vs_gas_readings := EL q kgss ++ tail') =
        OK (v with vs_gas_readings := tail') /\
        gas_events_step f C sf.fn_name (EL q pre) (u with vs_gas_readings := EL q kgss ++ tail') = EL q ess))) ==>
  (?extra. FLAT ess = gas_events_block f C sf.fn_name eb
    (s with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
  (!u. FOLDR (dft_exec_cons f C) OK pre (s with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
    gas_events_block f C sf.fn_name eb (s with vs_gas_readings := FLAT kgss ++ tail) = FLAT ess /\
    u.vs_gas_readings = tail /\
    trace_gas (trace_block a e f C sf tb (s with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT ks,FLAT kgss) /\
    (!tail'. FOLDR (dft_exec_cons f C) OK pre (s with vs_gas_readings := FLAT kgss ++ tail') =
        OK (u with vs_gas_readings := tail') /\
      gas_events_block f C sf.fn_name eb (s with vs_gas_readings := FLAT kgss ++ tail') = FLAT ess))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[LENGTH_NIL, DROP_EQ_NIL] >>
      simp[Once gas_events_defs, Once trace_defs, get_instruction_def, trace_gas_def] >>
      rpt strip_tac >> gvs[] >> simp[Once gas_events_defs, get_instruction_def]) >>
  namedCases_on `kgss` ["", "row rows"] >> gvs[] >>
  namedCases_on `ess` ["", "es ess0"] >> gvs[] >>
  rename1 `LIST_REL (\keys ws. LENGTH keys = LENGTH ws) kss rows` >>
  `s.vs_inst_idx < LENGTH eb.bb_instructions /\ s.vs_inst_idx < LENGTH tb.bb_instructions` by
    (qpat_x_assum `DROP _ eb.bb_instructions = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     qpat_x_assum `DROP _ tb.bb_instructions = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `get_instruction eb s.vs_inst_idx = SOME h /\ get_instruction tb s.vs_inst_idx = SOME h /\
   DROP (SUC s.vs_inst_idx) eb.bb_instructions = pre /\
   DROP (SUC s.vs_inst_idx) tb.bb_instructions = pre` by
    gvs[DROP_CONS_EL, get_instruction_def] >>
  qpat_assum `!q rest u. _` (qspecl_then [`0`, `s.vs_gas_readings`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `step_inst f C h (s with vs_gas_readings := row ++ FLAT rows ++ tail)`
  >- suspend "success"
  >> (simp[Once gas_events_defs, dft_exec_cons_def] >>
      qpat_x_assum `!kgss ess' ks' s'' eb' tb' tail. _` kall_tac >>
      qpat_x_assum `!q rest u. _` kall_tac >>
      qpat_x_assum `!tail v. _` kall_tac >>
      qpat_x_assum `!tail. ?extra. _` (qspec_then `FLAT rows ++ tail` strip_assume_tac) >>
      qexists_tac `extra ++ FLAT ess0` >> simp[APPEND_ASSOC])
QED

Resume native_replay_list[success]:
  rename1 `step_inst f C h (s with vs_gas_readings := row ++ FLAT rows ++ tail) = OK v` >>
  qpat_assum `!tail v. step_inst _ _ _ _ = _ ==> _`
    (qspecl_then [`FLAT rows ++ tail`, `v`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!kgss ess' ks' s'' eb' tb' tail. _`
    (qspecl_then [`rows`, `ess0`, `kss`, `v with vs_inst_idx := SUC s.vs_inst_idx`,
      `eb`, `tb`, `tail`] mp_tac) >>
  (impl_tac >- (
    simp[] >> rpt gen_tac >> disch_then strip_assume_tac >>
    qpat_assum `!tail'. step_inst _ _ _ _ = _ /\ _`
      (qspec_then `FLAT (TAKE q rows) ++ rest` strip_assume_tac) >>
    fs[APPEND_ASSOC] >>
    qpat_x_assum `!q rest u. _`
      (qspecl_then [`SUC q`, `rest`, `u`] mp_tac) >>
    (impl_tac >- simp[dft_exec_cons_def]) >>
    POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[])) >>
  `v with vs_gas_readings := FLAT rows ++ tail = v` by (
    qpat_assum `step_inst _ _ _ _ = OK v` mp_tac >>
    qpat_assum `!tail'. step_inst _ _ _ _ = _ /\ _`
      (qspec_then `FLAT rows ++ tail` mp_tac) >>
    POP_ASSUM_LIST (K all_tac) >> simp[APPEND_ASSOC] >> metis_tac[]) >>
  simp[] >> strip_tac >>
  conj_tac
  >- (qexists_tac `extra` >> once_rewrite_tac[gas_events_defs] >> simp[APPEND_ASSOC]) >>
  qpat_x_assum `!q rest u. _` kall_tac >>
  qpat_x_assum `!tail v. _` kall_tac >>
  qpat_x_assum `!tail. ?extra. _` kall_tac >>
  gen_tac >> pure_rewrite_tac[dft_exec_cons_def] >> asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `!u. FOLDR _ _ _ _ = OK u ==> _` drule >> strip_tac >>
  FAIL_TAC "success compose"
QED

Finalise native_replay_list
