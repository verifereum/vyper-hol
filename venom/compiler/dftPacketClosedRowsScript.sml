Theory dftPacketClosedRows
Ancestors
  dftPacketFillingBoundary dftGasFromListTraceDefs dftGasFromListReadings dftGasToListReplay
  dftRunRel crossBlockSimProofs gasEvents venomExecSemantics
  passSimulationDefs venomState list rich_list arithmetic sorting

Theorem dft_packet_closed_rows_conservation:
  !mss ess kss entries out.
    0 < LENGTH mss /\ LENGTH ess = LENGTH mss /\
    LENGTH kss = LENGTH mss /\ LENGTH entries = LENGTH mss /\
    (!i. i < LENGTH mss ==>
      EVERY IS_SOME (EL i mss) /\
      LENGTH (EL i mss) = LENGTH (EL i ess) /\
      LENGTH (EL i mss) = LENGTH (EL i kss) /\
      PERM (MAP THE (EL i mss) ++
        (if SUC i < LENGTH mss then (EL (SUC i) entries).vs_gas_readings
         else out.vs_gas_readings)) (EL i entries).vs_gas_readings) ==>
    EVERY IS_SOME (FLAT mss) /\
    LENGTH (FLAT mss) = LENGTH (FLAT ess) /\
    LENGTH (FLAT mss) = LENGTH (FLAT kss) /\
    PERM (MAP THE (FLAT mss) ++ out.vs_gas_readings)
      (HD entries).vs_gas_readings
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `ess` >> Cases_on `kss` >> Cases_on `entries` >> gvs[] >>
  qpat_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  Cases_on `mss = []`
  >- gvs[] >>
  `EVERY IS_SOME (FLAT mss) /\
   LENGTH (FLAT mss) = LENGTH (FLAT t) /\
   LENGTH (FLAT mss) = LENGTH (FLAT t') /\
   PERM (MAP THE (FLAT mss) ++ out.vs_gas_readings)
      (HD t'').vs_gas_readings` by
    (first_x_assum irule >> simp[] >>
     reverse conj_tac >- (Cases_on `mss` >> gvs[]) >>
     qx_gen_tac `i` >> strip_tac >>
     qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >> simp[]) >>
  simp[] >>
  irule PERM_TRANS >>
  qexists_tac `MAP THE h ++ (HD t'').vs_gas_readings` >>
  conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      metis_tac[PERM_APPEND_IFF]) >>
  qpat_x_assum `PERM (MAP THE h ++ _) _` mp_tac >>
  Cases_on `mss` >> gvs[]
QED

Theorem dft_packet_closed_rows_target:
  !bbs bts entries N C tf inc ir out.
    0 < LENGTH bbs /\ inc + LENGTH bbs <= N /\
    LENGTH bts = LENGTH bbs /\ LENGTH entries = LENGTH bbs /\
    (!i. i < LENGTH bbs ==>
      lookup_block (EL i entries).vs_current_bb tf.fn_blocks = SOME (EL i bts) /\
      (SUC i < LENGTH bbs ==> ~(EL (SUC i) entries).vs_halted) /\
      (!F. N <= F ==> run_block (F-(inc+SUC i)) C (EL i bts) (EL i entries) =
        (if SUC i < LENGTH bbs then OK (EL (SUC i) entries)
         else IntRet ir out))) ==>
    !F. N <= F ==> run_blocks (F-inc) C tf (HD entries) = IntRet ir out
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `bts` >> Cases_on `entries` >> gvs[] >>
  qpat_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  rpt strip_tac >> rename1 `run_blocks (fuel-inc) C tf _ = _` >>
  `fuel-inc = SUC (fuel-(inc+1))` by decide_tac >>
  asm_rewrite_tac[run_blocks_unfold] >> simp[] >>
  Cases_on `bbs = []` >- gvs[] >>
  `run_blocks (fuel-(inc+1)) C tf (HD t') = IntRet ir out` suffices_by
    (Cases_on `t'` >> gvs[]) >>
  `0 < LENGTH bbs` by (Cases_on `bbs` >> gvs[]) >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`N`,`t`] >> simp[] >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >>
  simp[]
  >> (simp [SUC_ONE_ADD])
QED

Theorem dft_packet_closed_row_enter:
  !f C sf bb s sp r a inc.
    lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK sp /\ run_block f C bb s = r ==>
    run_blocks (SUC f) C sf s =
      (case r of OK v => if v.vs_halted then Halt v else run_blocks f C sf v
       | other => other) /\
    gas_events_blocks (SUC f) C sf s =
      gas_events_block f C sf.fn_name bb
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) ++
      (case r of OK v => if v.vs_halted then [] else gas_events_blocks f C sf v
       | other => []) /\
    trace_gas (trace_blocks a inc (SUC f) C sf s) =
      trace_gas (trace_block a (SUC inc) f C sf bb
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) ++
      (case r of OK v => if v.vs_halted then [] else
         trace_gas (trace_blocks a (SUC inc) f C sf v)
       | other => [])
Proof
  rpt gen_tac >> strip_tac >>
  `exec_block f C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = r`
    by gvs[run_block_def] >>
  drule_all trace_blocks_enter >> strip_tac >>
  simp[Once gas_events_blocks_def, run_blocks_unfold] >>
  Cases_on `r` >> simp[] >> Cases_on `v.vs_halted` >> simp[]
QED

Theorem dft_packet_closed_row_terminating_head:
  !f C sf s bb.
    lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
    terminates (run_blocks f C sf s) ==>
    ?g. terminates (run_block g C bb s)
Proof
  Cases >- simp[Once run_blocks_def, terminates_def] >> rpt strip_tac >>
  qexists_tac `n` >>
  qpat_x_assum `terminates _` mp_tac >>
  simp[run_blocks_unfold] >>
  Cases_on `run_block n C bb s` >> simp[terminates_def]
QED

Theorem dft_packet_closed_row_terminating_tail:
  !C sf bb s N inc next tail.
    lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\ ~next.vs_halted /\
    (!F. N <= F ==>
      ((?g. terminates (run_block g C bb s)) ==>
       residual_result tail (OK next) (run_block (F-SUC inc) C bb s))) /\
    (?f. terminates (run_blocks f C sf s)) ==>
    ?f. terminates (run_blocks f C sf (next with vs_gas_readings := tail))
Proof
  rpt strip_tac >>
  `?g. terminates (run_block g C bb s)` by
    metis_tac[dft_packet_closed_row_terminating_head] >>
  drule run_blocks_fuel_mono >>
  disch_then (qspec_then `N + SUC inc` mp_tac) >> strip_tac >>
  `f + (N + SUC inc) = SUC (f + N + inc)` by decide_tac >>
  `run_block (f+N+inc) C bb s = OK (next with vs_gas_readings := tail)` by
    (first_x_assum (qspec_then `f+N+inc+SUC inc` mp_tac) >> simp[] >> metis_tac[]) >>
  qexists_tac `f+N+inc` >>
  qpat_x_assum `terminates _` mp_tac >>
  qpat_x_assum `run_blocks _ _ _ _ = _` (mp_tac o GSYM) >>
  simp[run_blocks_unfold]
  >> (gvs[venomExecSemanticsTheory.exec_result_case_eq])
QED
