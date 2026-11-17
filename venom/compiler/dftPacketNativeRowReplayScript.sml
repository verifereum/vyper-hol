Theory dftPacketNativeRowReplay
Ancestors
  dftIndexedExec dftGasFromListTraceDefs dftGasFromListReadings dftGasToListReplay
  gasOracleReplay gasEvents frameGasEvents stateEquiv
  venomExecSemantics venomState venomInst list rich_list arithmetic

Theorem native_plain_step[local]:
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  step_inst f C i s = OK u ==>
  u.vs_gas_readings = s.vs_gas_readings /\
  !tail. step_inst f C i (s with vs_gas_readings := tail) =
    OK (u with vs_gas_readings := tail)
Proof
  strip_tac >>
  `gas_replay_at 0 (step_inst_base i) s` by
    (irule gas_base_non_gas >> simp[]) >>
  gvs[gas_replay_at_def, step_inst_def] >>
  reverse conj_tac
  >- (gen_tac >> first_x_assum (qspec_then `tail` mp_tac) >>
      Cases_on `step_inst_base i (s with vs_gas_readings := tail)` >>
      simp[lift_result_def]) >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  Cases_on `step_inst_base i (s with vs_gas_readings := [])` >>
  simp[lift_result_def]
QED

Theorem native_gas_step[local]:
  i.inst_opcode = GAS /\
  step_inst f C i (s with vs_gas_readings := w::tail) = OK u ==>
  u.vs_gas_readings = tail /\
  !tail'. step_inst f C i (s with vs_gas_readings := w::tail') =
    OK (u with vs_gas_readings := tail')
Proof
  simp[step_inst_def] >> strip_tac >>
  gvs[step_inst_base_def, exec_gas_def, AllCaseEqs()] >> simp[]
QED

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
  qpat_x_assum `_ = OK u`
    (assume_tac o SRULE []) >>
  qpat_x_assum `!u. FOLDR _ _ _ _ = OK u ==> _` drule >> strip_tac >>
  `extra = []` by (
    qpat_x_assum `FLAT ess0 = _` mp_tac >> simp[]) >>
  qpat_x_assum `FLAT ess0 = _` kall_tac >>
  simp[] >> conj_tac
  >- (once_rewrite_tac[gas_events_defs] >> simp[]) >>
  conj_tac
  >- (once_rewrite_tac[trace_defs] >>
      simp[GSYM trace_gas_def, APPEND_ASSOC] >>
      once_rewrite_tac[GSYM APPEND_ASSOC] >> simp[] >>
      irule ZIP_APPEND >> simp[] >>
      `MAP LENGTH kss = MAP LENGTH rows` by simp[MAP_EQ_LIST_REL] >>
      simp[LENGTH_FLAT]) >>
  gen_tac >>
  qpat_assum `!tail'. step_inst _ _ _ _ = _ /\ _`
    (qspec_then `FLAT rows ++ tail'` strip_assume_tac) >>
  qpat_assum `!tail'. FOLDR _ _ _ _ = _ /\ _`
    (qspec_then `tail'` strip_assume_tac) >>
  fs[APPEND_ASSOC] >> once_rewrite_tac[gas_events_defs] >>
  simp[APPEND_ASSOC]
QED

Finalise native_replay_list

Theorem dft_packet_native_row_replay:
  bb.bb_instructions = ps ++ xs /\ be.vs_inst_idx = LENGTH ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\ k <= LENGTH xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
  LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH xs /\ LENGTH ks = LENGTH xs /\
  LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
  LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
  (!q. q < k ==>
    ((EL q xs).inst_opcode = GAS ==>
      EL q ess = [(sf.fn_name,(EL q xs).inst_id)] /\
      EL q ks = [(a,e,(EL q xs).inst_id)] /\ ?slot. EL q ms = [slot]) /\
    ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
      EL q ms = [] /\ EL q ess = [] /\ EL q ks = [])) /\
  (!q pg rest u ws.
    q < k /\ (EL q xs).inst_opcode = INVOKE /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) pg /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL q ms) ws /\
    FOLDR (dft_exec_cons f C) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT pg ++ rest) = OK u ==>
    (!tail. ?extra. EL q ess = gas_events_step f C sf.fn_name (EL q xs)
      (u with vs_gas_readings := ws ++ tail) ++ extra) /\
    (!tail v. step_inst f C (EL q xs) (u with vs_gas_readings := ws ++ tail) = OK v ==>
      gas_events_step f C sf.fn_name (EL q xs) (u with vs_gas_readings := ws ++ tail) = EL q ess /\
      v.vs_gas_readings = tail /\
      trace_gas (trace_step a e f C sf (EL q xs) (u with vs_gas_readings := ws ++ tail)) =
        ZIP (EL q ks,ws) /\
      (!tail'. step_inst f C (EL q xs) (u with vs_gas_readings := ws ++ tail') =
        OK (v with vs_gas_readings := tail') /\
        gas_events_step f C sf.fn_name (EL q xs) (u with vs_gas_readings := ws ++ tail') = EL q ess))) /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
  (?extra. FLAT (TAKE k ess) =
    gas_events_block f C sf.fn_name
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
      (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
  (!u. FOLDR (dft_exec_cons f C) OK (TAKE k xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
    gas_events_block f C sf.fn_name
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
      (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
    u.vs_gas_readings = tail /\
    trace_gas (trace_block a e f C sf
      (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
      (be with vs_gas_readings := FLAT kgss ++ tail)) =
      ZIP (FLAT (TAKE k ks),FLAT kgss) /\
    (!tail'. FOLDR (dft_exec_cons f C) OK (TAKE k xs)
        (be with vs_gas_readings := FLAT kgss ++ tail') =
          OK (u with vs_gas_readings := tail') /\
      gas_events_block f C sf.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
        (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))
Proof
  strip_tac >> irule native_replay_list >>
  simp[DROP_APPEND, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
  `LENGTH kgss = k` by metis_tac[LIST_REL_LENGTH, LENGTH_TAKE, LESS_EQ_REFL] >>
  reverse conj_tac
  >- (conj_tac >- simp[] >>
      gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
      first_x_assum (qspec_then `n` mp_tac) >>
      simp[EL_TAKE] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  rpt gen_tac >> strip_tac >>
  `q < LENGTH xs /\ q < LENGTH ms /\ q < LENGTH kgss` by simp[] >>
  `q <= k` by simp[] >>
  fs[EL_TAKE, TAKE_TAKE_T] >>
  `LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
     (TAKE q ms) (TAKE q kgss)` by
    (drule LIST_REL_TAKE >> disch_then (qspec_then `q` mp_tac) >>
     simp[TAKE_TAKE_T]) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL q ms) (EL q kgss)` by
    (qpat_x_assum `LIST_REL _ (TAKE k ms) kgss` mp_tac >>
     simp[LIST_REL_EL_EQN, EL_TAKE] >> metis_tac[]) >>
  Cases_on `(EL q xs).inst_opcode = INVOKE`
  >- (qpat_x_assum `!q pg rest u ws. _`
        (qspecl_then [`q`, `TAKE q kgss`, `rest`, `u`, `EL q kgss`] mp_tac) >>
      (impl_tac >- simp[]) >>
      simp[visit_gas_def] >> POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qpat_x_assum `!q. q < k ==> _` (qspec_then `q` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `(EL q xs).inst_opcode = GAS`
  >- suspend "gas" >> suspend "plain"
QED

Resume dft_packet_native_row_replay[gas]:
  fs[] >>
  qpat_x_assum `LIST_REL _ (EL q ms) (EL q kgss)` mp_tac >> simp[] >> strip_tac >>
  simp[gas_events_step_plain, trace_step_noninvoke, trace_gas_def, visit_gas_def] >>
  rpt gen_tac >> strip_tac >> drule_all native_gas_step >> simp[]
QED

Resume dft_packet_native_row_replay[plain]:
  fs[] >>
  simp[gas_events_step_plain, trace_step_noninvoke, trace_gas_def, visit_gas_def] >>
  rpt gen_tac >> strip_tac >> drule_all native_plain_step >> simp[]
QED

Finalise dft_packet_native_row_replay
