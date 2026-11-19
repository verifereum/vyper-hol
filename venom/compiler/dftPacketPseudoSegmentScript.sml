Theory dftPacketPseudoSegment
Ancestors
  dftPacketInvokePrefixStop
  dftPacketEntryReplay dftPacketFreshRow dftPacketFillingBoundary
  dftPacketOperationalPrefix dftGasFromListTraceDefs dftGasFromListReadings
  dftIndexedExec gasEvents frameGasEvents venomExecSemantics
  venomInst venomState list rich_list arithmetic

Theorem pseudo_segment_step[local]:
  is_pseudo i.inst_opcode /\ s.vs_inst_idx = k /\
  step_inst g C8 i s = OK t /\ s1 = t with vs_inst_idx := SUC k ==>
  !f C7 gs. step_inst f C7 i (s with vs_gas_readings := gs) =
    OK (t with vs_gas_readings := gs)
Proof
  strip_tac >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    (Cases_on `i.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  `i.inst_opcode <> GAS` by
    (Cases_on `i.inst_opcode` >> gvs[is_pseudo_def]) >>
  gvs[step_inst_non_invoke] >> rpt gen_tac >>
  drule gasOracleReplayTheory.gas_base_non_gas >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[gasOracleReplayTheory.gas_replay_at_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  Cases_on `step_inst_base i (s with vs_gas_readings := gs)` >>
  simp[stateEquivTheory.lift_result_def]
QED

Theorem dft_packet_pseudo_segment:
  !bb ps xs k s g C8 t s1 q segment ms ess ks M E K H f C7 sf a e.
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  k < LENGTH ps /\ s.vs_inst_idx = k /\
  step_inst g C8 (EL k ps) s = OK t /\
  s1 = t with vs_inst_idx := SUC k /\
  ((SUC k < LENGTH ps /\ segment = [EL k ps] /\ M = [] /\ E = [] /\ K = []) \/
   (SUC k = LENGTH ps /\ q < LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q xs) /\
    segment = [EL k ps] ++ TAKE q xs /\
    ms = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs) /\
    ess = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(sf.fn_name,(EL r xs).inst_id)] else []) (LENGTH xs) /\
    ks = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(a,e,(EL r xs).inst_id)] else []) (LENGTH xs) /\
    M = FLAT (TAKE q ms) /\ E = FLAT (TAKE q ess) /\ K = FLAT (TAKE q ks))) /\
  H = (\v. (gas_events_block f C7 sf.fn_name
    (bb with bb_instructions := TAKE (k + LENGTH segment) bb.bb_instructions) v,
    FOLDR (dft_exec_cons f C7) OK segment v)) ==>
  LENGTH M = LENGTH E /\ LENGTH M = LENGTH K /\
  segment = TAKE (LENGTH segment) (DROP k bb.bb_instructions) /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) segment /\
  (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M gs ==>
    (?extra. E = FST (H (s with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (!ev u. H (s with vs_gas_readings := gs ++ tail) = (ev,OK u) ==>
      ev = E /\ u.vs_gas_readings = tail /\
      trace_gas (trace_block a e f C7 sf
        (bb with bb_instructions := TAKE (k + LENGTH segment) bb.bb_instructions)
        (s with vs_gas_readings := gs ++ tail)) = ZIP (K,gs) /\
      (!tail'. H (s with vs_gas_readings := gs ++ tail') =
        (E,OK (u with vs_gas_readings := tail')))) /\
    (!ir u. SND (H (s with vs_gas_readings := gs ++ tail)) <> IntRet ir u)) /\
  (SUC k < LENGTH ps ==> !gs. H (s with vs_gas_readings := gs) =
    ([],OK (s1 with vs_gas_readings := gs)))
Proof
  rpt gen_tac >> strip_tac >>
  `is_pseudo (EL k ps).inst_opcode` by fs[EVERY_EL] >>
  `~is_terminator (EL k ps).inst_opcode /\
   (EL k ps).inst_opcode <> INVOKE /\ (EL k ps).inst_opcode <> GAS` by
    (Cases_on `(EL k ps).inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  `!gs. step_inst f C7 (EL k ps) (s with vs_gas_readings := gs) =
    OK (t with vs_gas_readings := gs)` by
    (irule pseudo_segment_step >> metis_tac[])
  >- suspend "interior"
  >> suspend "boundary"
QED

Resume dft_packet_pseudo_segment[interior]:
  `get_instruction
     (bb with bb_instructions := TAKE (SUC k) bb.bb_instructions) k =
     SOME (EL k ps)` by
    simp[get_instruction_def,EL_TAKE,EL_APPEND1,LENGTH_TAKE] >>
  `!gs. H (s with vs_gas_readings := gs) =
     ([],OK (s1 with vs_gas_readings := gs))` by
    (gen_tac >> simp[dft_exec_cons_def,ADD1] >>
     simp[Once gas_events_defs,gas_events_step_plain,get_instruction_def,
          EL_TAKE,EL_APPEND1,LENGTH_TAKE] >>
     simp[Once gas_events_defs,get_instruction_def,LENGTH_TAKE]) >>
  qpat_x_assum `H = _` kall_tac >>
  simp[TAKE1_DROP,EL_APPEND1] >>
  rpt gen_tac >>
  simp[Once trace_defs,get_instruction_def,EL_TAKE,EL_APPEND1,
       LENGTH_TAKE,trace_gas_cons,visit_gas_def,trace_step_noninvoke,ADD1] >>
  simp[Once trace_defs,get_instruction_def,LENGTH_TAKE,trace_gas_def]
QED

Resume dft_packet_pseudo_segment[boundary]:
  `LENGTH M = LENGTH E /\ LENGTH M = LENGTH K'` by
    simp[GENLIST_EL_MAP,GSYM MAP_TAKE,LENGTH_FLAT,MAP_MAP_o,combinTheory.o_DEF,COND_RAND] >>
  `DROP k ps = [EL k ps]` by
    simp[Once DROP_CONS_EL] >>
  `segment = TAKE (LENGTH segment) (DROP k bb.bb_instructions) /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) segment` by
    simp[DROP_APPEND1,TAKE_APPEND,LENGTH_TAKE] >>
  `k + LENGTH segment = LENGTH ps + q` by simp[] >>
  `s1.vs_inst_idx = LENGTH ps` by simp[] >>
  `!gs. H (s with vs_gas_readings := gs) =
    (gas_events_block f C7 sf.fn_name
      (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
      (s1 with vs_gas_readings := gs),
     FOLDR (dft_exec_cons f C7) OK (TAKE q xs) (s1 with vs_gas_readings := gs))` by
    (gen_tac >> simp[dft_exec_cons_def] >>
     simp[Once gas_events_defs,get_instruction_def,EL_TAKE,EL_APPEND1,
          LENGTH_TAKE,gas_events_step_plain] >> simp[]) >>
  `!gs. gas_events_block f C7 sf.fn_name
    (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
    (s1 with vs_gas_readings := gs) =
    gas_events_block f C7 sf.fn_name
      <|bb_label := s1.vs_current_bb; bb_instructions :=
        REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE q xs|>
      (s1 with vs_gas_readings := gs)` by
    (gen_tac >> irule gas_events_block_suffix_cong >> qexists `TAKE q xs` >>
     simp[DROP_TAKE,DROP_APPEND]) >>
  `!gs. trace_gas (trace_block a e f C7 sf
    (bb with bb_instructions := TAKE (k + LENGTH segment) bb.bb_instructions)
    (s with vs_gas_readings := gs)) =
    trace_gas (trace_block a e f C7 sf
    (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
    (s1 with vs_gas_readings := gs))` by
    (gen_tac >> simp[Once trace_defs,get_instruction_def,EL_TAKE,EL_APPEND1,
       LENGTH_TAKE,trace_gas_cons,visit_gas_def,trace_step_noninvoke] >> simp[]) >>
  qpat_x_assum `H = _` kall_tac >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q ms)) gs` by
    metis_tac[] >>
  drule dft_packet_flat_filling_split >> strip_tac >>
  `q <= LENGTH xs` by decide_tac >>
  drule_all dft_packet_fresh_row_replay >>
  disch_then (qspecl_then [`tail`,`f`,`C7`] strip_assume_tac) >>
  conj_tac >- (simp[] >> metis_tac[]) >>
  reverse conj_tac
  >- (rpt gen_tac >> simp[] >> irule dft_packet_nonterminator_prefix_no_intret >> fs[EVERY_CONJ]) >>
  suspend "boundary_success"
QED

Resume dft_packet_pseudo_segment[boundary_success]:
  qpat_x_assum `segment = TAKE _ _` kall_tac >>
  qpat_x_assum `segment = _` kall_tac >>
  qpat_x_assum `bb.bb_instructions = _` kall_tac >>
  qpat_x_assum `ms = _` kall_tac >>
  qpat_x_assum `ess = _` kall_tac >>
  qpat_x_assum `ks = _` kall_tac >>
  qpat_x_assum `gs = FLAT _` SUBST_ALL_TAC >>
  rpt gen_tac >>
  qpat_assum `!gs. H _ = _`
    (fn th => pure_rewrite_tac[th,pairTheory.PAIR_EQ]) >> strip_tac >>
  qpat_x_assum `!u. FOLDR _ _ _ _ = OK u ==> _` drule >>
  strip_tac >>
  qpat_x_assum `gas_events_block _ _ _ _ _ = ev` (SUBST1_TAC o SYM) >>
  qpat_assum `!gs. trace_gas _ = _`
    (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `!gs. gas_events_block _ _ _ _ _ = _`
    (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `E = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `K' = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `!tail'. FOLDR _ _ _ _ = _ /\ _`
    (fn th => simp[NoAsms,th]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `trace_gas _ = ZIP _` mp_tac >>
  simp[NoAsms,ADD_COMM]
QED

Finalise dft_packet_pseudo_segment
