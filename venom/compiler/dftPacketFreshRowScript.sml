Theory dftPacketFreshRow
Ancestors
  dftIndexedExec dftGasFromListTraceDefs dftGasFromListReadings dftGasToListReplay
  gasOracleReplay gasEvents frameGasEvents stateEquiv
  venomExecSemantics venomState venomInst list rich_list arithmetic

Theorem fresh_plain_step[local]:
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

Theorem fresh_gas_step[local]:
  i.inst_opcode = GAS /\
  step_inst f C i (s with vs_gas_readings := w::tail) = OK u ==>
  u.vs_gas_readings = tail /\
  !tail'. step_inst f C i (s with vs_gas_readings := w::tail') =
    OK (u with vs_gas_readings := tail')
Proof
  simp[step_inst_def] >> strip_tac >>
  gvs[step_inst_base_def, exec_gas_def, AllCaseEqs()] >> simp[]
QED

Theorem fresh_replay_list[local]:
  !pre kgss s eb tb tail.
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) pre /\
  DROP s.vs_inst_idx eb.bb_instructions = pre /\
  DROP s.vs_inst_idx tb.bb_instructions = pre /\
  LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
    (MAP (\i. if i.inst_opcode = GAS then [NONE] else []) pre) kgss ==>
  (?extra. FLAT (MAP (\i. if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else []) pre) =
    gas_events_block f C sf.fn_name eb
      (s with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
  (!u. FOLDR (dft_exec_cons f C) OK pre
      (s with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
    gas_events_block f C sf.fn_name eb
      (s with vs_gas_readings := FLAT kgss ++ tail) =
        FLAT (MAP (\i. if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else []) pre) /\
    u.vs_gas_readings = tail /\
    trace_gas (trace_block a e f C sf tb
      (s with vs_gas_readings := FLAT kgss ++ tail)) =
      ZIP (FLAT (MAP (\i. if i.inst_opcode = GAS then [(a,e,i.inst_id)] else []) pre),FLAT kgss) /\
    (!tail'. FOLDR (dft_exec_cons f C) OK pre
        (s with vs_gas_readings := FLAT kgss ++ tail') =
          OK (u with vs_gas_readings := tail') /\
      gas_events_block f C sf.fn_name eb
        (s with vs_gas_readings := FLAT kgss ++ tail') =
          FLAT (MAP (\i. if i.inst_opcode = GAS then [(sf.fn_name,i.inst_id)] else []) pre)))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[DROP_EQ_NIL] >> rpt conj_tac >> rpt gen_tac >>
      simp[Once gas_events_defs, Once trace_defs, get_instruction_def,
           trace_gas_def] >> rpt strip_tac >> gvs[] >>
      simp[Once gas_events_defs, get_instruction_def]) >>
  namedCases_on `kgss` ["", "row rows"] >> gvs[] >>
  `s.vs_inst_idx < LENGTH eb.bb_instructions /\
   s.vs_inst_idx < LENGTH tb.bb_instructions` by
    (qpat_x_assum `DROP _ eb.bb_instructions = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     qpat_x_assum `DROP _ tb.bb_instructions = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `get_instruction eb s.vs_inst_idx = SOME h /\
   EL s.vs_inst_idx eb.bb_instructions = h /\
   EL s.vs_inst_idx tb.bb_instructions = h /\
   get_instruction tb s.vs_inst_idx = SOME h /\ 
   DROP (SUC s.vs_inst_idx) eb.bb_instructions = pre /\
   DROP (SUC s.vs_inst_idx) tb.bb_instructions = pre` by
    gvs[DROP_CONS_EL, get_instruction_def] >>
  Cases_on `h.inst_opcode = GAS`
  >- suspend "gas"
  >> suspend "plain"
QED

Resume fresh_replay_list[gas]:
  fs[] >>
  simp[Once gas_events_defs, Once trace_defs, get_instruction_def,
       trace_gas_cons, visit_gas_def, trace_step_noninvoke, gas_events_step_plain] >>
  Cases_on `step_inst f C h (s with vs_gas_readings := w::(FLAT rows ++ tail))`
  >- suspend "gas_ok"
  >> simp[dft_exec_cons_def] >> metis_tac[]
QED

Resume fresh_replay_list[plain]:
  fs[] >>
  simp[Once gas_events_defs, Once trace_defs, get_instruction_def,
       trace_gas_cons, visit_gas_def, trace_step_noninvoke, gas_events_step_plain] >>
  Cases_on `step_inst f C h (s with vs_gas_readings := FLAT rows ++ tail)`
  >- suspend "plain_ok"
  >> simp[dft_exec_cons_def] >> metis_tac[]
QED

Resume fresh_replay_list[gas_ok]:
  drule_all fresh_gas_step >> strip_tac >>
  first_x_assum (qspecl_then [`rows`, `v with vs_inst_idx := SUC s.vs_inst_idx`,
    `eb`, `tb`, `tail`] mp_tac) >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  `v with <|vs_inst_idx := SUC s.vs_inst_idx;
     vs_gas_readings := FLAT rows ++ tail|> =
   v with vs_inst_idx := SUC s.vs_inst_idx` by
    simp[venom_state_component_equality] >>
  conj_tac >- metis_tac[] >>
  gen_tac >>
  pure_rewrite_tac[dft_exec_cons_def] >>
  qpat_assum `!tail'. step_inst _ _ _ _ = _`
    (qspec_then `FLAT rows ++ tail` mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_assum `v with <|vs_inst_idx := _; vs_gas_readings := _|> = _`
    (fn eqth => qpat_x_assum `!u. FOLDR _ _ _ _ = OK u ==> _`
      (mp_tac o PURE_REWRITE_RULE [eqth])) >>
  disch_then drule >> strip_tac >>
  `extra = []` by metis_tac[APPEND_NIL, APPEND_11] >>
  qpat_x_assum `_ = _ ++ extra` kall_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK v` kall_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK (v with vs_gas_readings := _)` kall_tac >>
  simp[Once gas_events_defs, get_instruction_def, gas_events_step_plain] >>
  gen_tac >>
  simp[Once gas_events_defs, get_instruction_def, gas_events_step_plain]
QED

Resume fresh_replay_list[plain_ok]:
  drule_all fresh_plain_step >> simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`rows`, `v with vs_inst_idx := SUC s.vs_inst_idx`,
    `eb`, `tb`, `tail`] mp_tac) >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  `v with <|vs_inst_idx := SUC s.vs_inst_idx;
     vs_gas_readings := FLAT rows ++ tail|> =
   v with vs_inst_idx := SUC s.vs_inst_idx` by
    simp[venom_state_component_equality] >>
  conj_tac >- metis_tac[] >>
  gen_tac >> pure_rewrite_tac[dft_exec_cons_def] >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `_ = OK u`
    (assume_tac o SRULE []) >>
  qpat_assum `v with <|vs_inst_idx := _; vs_gas_readings := _|> = _`
    (fn eqth => qpat_x_assum `!u. FOLDR _ _ _ _ = OK u ==> _`
      (mp_tac o PURE_REWRITE_RULE [eqth])) >>
  disch_then drule >> strip_tac >>
  `extra = []` by metis_tac[APPEND_NIL, APPEND_11] >>
  qpat_x_assum `_ = _ ++ extra` kall_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK v` kall_tac >>
  simp[Once gas_events_defs, get_instruction_def, gas_events_step_plain] >>
  gen_tac >>
  simp[Once gas_events_defs, get_instruction_def, gas_events_step_plain]
QED

Finalise fresh_replay_list

(* The source-indexed initial tables satisfy U before any INVOKE is visited. *)
Theorem dft_packet_fresh_row_replay:
  bb.bb_instructions = ps ++ xs /\ be.vs_inst_idx = LENGTH ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  k <= LENGTH xs /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE k xs) /\
  ms = GENLIST (\q. if (EL q xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs) /\
  ess = GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(sf.fn_name,(EL q xs).inst_id)] else []) (LENGTH xs) /\
  ks = GENLIST (\q. if (EL q xs).inst_opcode = GAS then [(a,e,(EL q xs).inst_id)] else []) (LENGTH xs) /\
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
    (!tail'.
      FOLDR (dft_exec_cons f C) OK (TAKE k xs)
        (be with vs_gas_readings := FLAT kgss ++ tail') =
          OK (u with vs_gas_readings := tail') /\
      gas_events_block f C sf.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
        (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))
Proof
  strip_tac >>
  gvs[GENLIST_EL_MAP, GSYM MAP_TAKE] >>
  irule fresh_replay_list >>
  simp[DROP_APPEND, TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED
