Theory dftPacketClosedRows
Ancestors
  dftPacketFillingBoundary dftGasFromListTraceDefs dftGasFromListReadings
  dftGasFromListRestore dftGasToListReplay
  dftRunRel crossBlockSimProofs gasEvents venomExecSemantics
  passSimulationDefs stateEquiv venomState list rich_list arithmetic sorting

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

Theorem dft_packet_residual_intret[local]:
  !ws ir out r. residual_result ws (IntRet ir out) r <=>
    r = IntRet ir (out with vs_gas_readings := ws)
Proof
  rpt gen_tac >> Cases_on `r` >> simp[residual_result_def, lift_result_def] >> metis_tac[]
QED

Theorem dft_packet_closed_rows_source:
  !bbs entries mss ess kss N C sf a inc ir out.
    0 < LENGTH bbs /\ inc + LENGTH bbs <= N /\
    LENGTH entries = LENGTH bbs /\ LENGTH mss = LENGTH bbs /\
    LENGTH ess = LENGTH bbs /\ LENGTH kss = LENGTH bbs /\
    (!i. i < LENGTH bbs ==>
      lookup_block (EL i entries).vs_current_bb sf.fn_blocks = SOME (EL i bbs) /\
      LENGTH (EL i kss) = LENGTH (EL i mss) /\
      (SUC i < LENGTH bbs ==> ~(EL (SUC i) entries).vs_halted) /\
      (?sp. eval_phis (EL i entries) (EL i bbs).bb_instructions = OK sp /\
        !F gs tail. N <= F /\
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL i mss) gs ==>
          (?extra. EL i ess =
            gas_events_block (F-(inc+SUC i)) C sf.fn_name (EL i bbs)
              (sp with <|vs_gas_readings := gs ++ tail;
                vs_inst_idx := phi_prefix_length (EL i bbs).bb_instructions|>) ++ extra) /\
          ((?f. terminates (run_block f C (EL i bbs)
              (EL i entries with vs_gas_readings := gs ++ tail))) ==>
            residual_result tail
              (if SUC i < LENGTH bbs then OK (EL (SUC i) entries) else IntRet ir out)
              (run_block (F-(inc+SUC i)) C (EL i bbs)
                (EL i entries with vs_gas_readings := gs ++ tail)) /\
            gas_events_block (F-(inc+SUC i)) C sf.fn_name (EL i bbs)
              (sp with <|vs_gas_readings := gs ++ tail;
                vs_inst_idx := phi_prefix_length (EL i bbs).bb_instructions|>) = EL i ess) /\
          (!v. (run_block (F-(inc+SUC i)) C (EL i bbs)
                  (EL i entries with vs_gas_readings := gs ++ tail) = OK v \/
                ?ret. run_block (F-(inc+SUC i)) C (EL i bbs)
                  (EL i entries with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
            trace_gas (trace_block a (inc+SUC i) (F-(inc+SUC i)) C sf (EL i bbs)
              (sp with <|vs_gas_readings := gs ++ tail;
                vs_inst_idx := phi_prefix_length (EL i bbs).bb_instructions|>)) =
                ZIP (EL i kss,gs)))) ==>
    !F gs tail. N <= F /\
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT mss) gs ==>
      LENGTH (FLAT kss) = LENGTH gs /\
      (?extra. FLAT ess = gas_events_blocks (F-inc) C sf
        (HD entries with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?f. terminates (run_blocks f C sf
          (HD entries with vs_gas_readings := gs ++ tail))) ==>
        run_blocks (F-inc) C sf (HD entries with vs_gas_readings := gs ++ tail) =
          IntRet ir (out with vs_gas_readings := tail) /\
        gas_events_blocks (F-inc) C sf
          (HD entries with vs_gas_readings := gs ++ tail) = FLAT ess) /\
      (!v. (run_blocks (F-inc) C sf (HD entries with vs_gas_readings := gs ++ tail) = OK v \/
            ?ret. run_blocks (F-inc) C sf
              (HD entries with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
        trace_gas (trace_blocks a inc (F-inc) C sf
          (HD entries with vs_gas_readings := gs ++ tail)) = ZIP (FLAT kss,gs))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  namedCases_on `entries` ["", "ent ents"] >>
  namedCases_on `mss` ["", "mask masks"] >>
  namedCases_on `ess` ["", "sites sitess"] >>
  namedCases_on `kss` ["", "keys keyss"] >> gvs[] >>
  qpat_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
  simp[NoAsms] >> strip_tac >> rename1 `eval_phis ent bb.bb_instructions = OK sp` >>
  map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> strip_tac >> gvs[LIST_REL_SPLIT1] >>
  rename1 `LIST_REL _ mask ghead` >>
  rename1 `LIST_REL _ (FLAT masks) grest` >>
  `LENGTH keys = LENGTH ghead` by metis_tac[LIST_REL_LENGTH] >>
  `fuel-inc = SUC (fuel-(inc+1))` by decide_tac >>
  `eval_phis (ent with vs_gas_readings := ghead ++ grest ++ tail) bb.bb_instructions =
     OK (sp with vs_gas_readings := ghead ++ grest ++ tail)` by
     (mp_tac (Q.SPECL [`bb.bb_instructions`,`ent`,`ghead ++ grest ++ tail`] replay_phis) >> simp[]) >>
  Cases_on `bbs = []`
  >- suspend "singleton" >>
  suspend "cons"
QED

Resume dft_packet_closed_rows_source[singleton]:
  qpat_x_assum `!i. i < SUC _ ==> _` kall_tac >> gvs[] >>
  qpat_x_assum `!F gs tail. _` (qspecl_then [`fuel`,`ghead`,`tail`] mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  Cases_on `?g. terminates (run_block g C bb (ent with vs_gas_readings := ghead ++ tail))`
  >- ((gvs[dft_packet_residual_intret] >>
      `lookup_block (ent with vs_gas_readings := ghead ++ tail).vs_current_bb sf.fn_blocks = SOME bb` by simp[] >>
      drule_all dft_packet_closed_row_enter >>
      disch_then (qspecl_then [`a`,`inc`] mp_tac) >>
      simp[] >> strip_tac >>
      `fuel-inc = SUC (fuel-(inc+1))` by decide_tac >>
      qpat_x_assum `fuel-inc = _` (fn th => rewrite_tac[th]) >>
      simp[GSYM ADD1] >> (gvs[dft_packet_residual_intret, GSYM ADD1, dft_packet_closed_row_enter]))) >>
  `?err. run_block (fuel-(inc+1)) C bb
      (ent with vs_gas_readings := ghead ++ tail) = Error err` by
    (qpat_assum `~(?g. terminates _)` mp_tac >>
     CONV_TAC (LAND_CONV NOT_EXISTS_CONV) >>
     disch_then (qspec_then `fuel-(inc+1)` mp_tac) >>
     Cases_on `run_block (fuel-(inc+1)) C bb (ent with vs_gas_readings := ghead ++ tail)` >>
     simp[terminates_def]) >>
  `lookup_block (ent with vs_gas_readings := ghead ++ tail).vs_current_bb sf.fn_blocks = SOME bb` by simp[] >>
  `~(?f. terminates (run_blocks f C sf (ent with vs_gas_readings := ghead ++ tail)))` by
    (strip_tac >> drule_all dft_packet_closed_row_terminating_head >> metis_tac[]) >>
  drule_all dft_packet_closed_row_enter >>
  disch_then (qspecl_then [`a`,`inc`] mp_tac) >> simp[] >> strip_tac >>
  `fuel-inc = SUC (fuel-(inc+1))` by decide_tac >>
  qpat_x_assum `fuel-inc = _` (fn th => rewrite_tac[th]) >> gvs[]
QED

Resume dft_packet_closed_rows_source[cons]:
  `0 < LENGTH bbs` by (Cases_on `bbs` >> gvs[]) >>
  `~(HD ents).vs_halted` by gvs[] >>
  `LENGTH (FLAT keyss) = LENGTH grest /\
   (?extra. FLAT sitess = gas_events_blocks (fuel-SUC inc) C sf
      (HD ents with vs_gas_readings := grest ++ tail) ++ extra) /\
   ((?f. terminates (run_blocks f C sf
       (HD ents with vs_gas_readings := grest ++ tail))) ==>
     run_blocks (fuel-SUC inc) C sf (HD ents with vs_gas_readings := grest ++ tail) =
       IntRet ir (out with vs_gas_readings := tail) /\
     gas_events_blocks (fuel-SUC inc) C sf
       (HD ents with vs_gas_readings := grest ++ tail) = FLAT sitess) /\
   (!v. (run_blocks (fuel-SUC inc) C sf
           (HD ents with vs_gas_readings := grest ++ tail) = OK v \/
         ?ret. run_blocks (fuel-SUC inc) C sf
           (HD ents with vs_gas_readings := grest ++ tail) = IntRet ret v) ==>
     trace_gas (trace_blocks a (SUC inc) (fuel-SUC inc) C sf
       (HD ents with vs_gas_readings := grest ++ tail)) = ZIP (FLAT keyss,grest))` by
    (first_x_assum irule >> simp[] >> qexistsl_tac [`N`,`masks`] >> simp[] >>
     qx_gen_tac `i` >> strip_tac >>
     qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >>
     simp[SUC_ONE_ADD]) >>
  qpat_x_assum `!i. i < SUC _ ==> _` kall_tac >>
  `lookup_block (ent with vs_gas_readings := ghead ++ grest ++ tail).vs_current_bb sf.fn_blocks = SOME bb` by simp[] >>
  `!F. N <= F ==>
    ((?g. terminates (run_block g C bb (ent with vs_gas_readings := ghead ++ grest ++ tail))) ==>
     residual_result (grest ++ tail) (OK (HD ents))
       (run_block (F-SUC inc) C bb (ent with vs_gas_readings := ghead ++ grest ++ tail)))` by
    ((qx_gen_tac `budget` >> rpt strip_tac >> qpat_x_assum `!F gs tail. _`
       (qspecl_then [`budget`,`ghead`,`grest ++ tail`] mp_tac) >> simp[GSYM ADD1] >> (metis_tac[GSYM ADD1]))) >>
  qpat_x_assum `!F gs tail. _` (qspecl_then [`fuel`,`ghead`,`grest ++ tail`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `?g. terminates (run_block g C bb (ent with vs_gas_readings := ghead ++ grest ++ tail))`
  >- suspend "cons_ok" >>
  suspend "cons_error"
QED

Resume dft_packet_closed_rows_source[cons_ok]:
  gvs[] >>
  `lookup_block (ent with vs_gas_readings := ghead ++ grest ++ tail).vs_current_bb sf.fn_blocks = SOME bb` by simp[] >>
  drule_all dft_packet_closed_row_enter >>
  disch_then (qspecl_then [`a`,`inc`] mp_tac) >> simp[] >> strip_tac >>
  gvs[GSYM ADD1] >>
  conj_tac
  >- (strip_tac >>
      `?f. terminates (run_blocks f C sf (HD ents with vs_gas_readings := grest ++ tail))` by
        (irule dft_packet_closed_row_terminating_tail >> simp[] >>
         qexistsl_tac [`N`,`bb`,`inc`,`ent with vs_gas_readings := ghead ++ grest ++ tail`] >>
         simp[] >> metis_tac[]) >>
      metis_tac[]) >>
  rpt strip_tac >>
  `LENGTH keys = LENGTH ghead` by metis_tac[LIST_REL_LENGTH] >>
  simp[ZIP_APPEND] >> metis_tac[]
QED

Resume dft_packet_closed_rows_source[cons_error]:
  `?err. run_block (fuel-(inc+1)) C bb
      (ent with vs_gas_readings := ghead ++ grest ++ tail) = Error err` by
    (qpat_assum `~(?g. terminates _)` mp_tac >>
     CONV_TAC (LAND_CONV NOT_EXISTS_CONV) >>
     disch_then (qspec_then `fuel-(inc+1)` mp_tac) >>
     Cases_on `run_block (fuel-(inc+1)) C bb (ent with vs_gas_readings := ghead ++ grest ++ tail)` >>
     simp[terminates_def]) >>
  `lookup_block (ent with vs_gas_readings := ghead ++ grest ++ tail).vs_current_bb sf.fn_blocks = SOME bb` by simp[] >>
  `~(?f. terminates (run_blocks f C sf (ent with vs_gas_readings := ghead ++ grest ++ tail)))` by
    (strip_tac >> drule_all dft_packet_closed_row_terminating_head >> metis_tac[]) >>
  drule_all dft_packet_closed_row_enter >>
  disch_then (qspecl_then [`a`,`inc`] mp_tac) >> simp[] >> strip_tac >>
  `fuel-inc = SUC (fuel-(inc+1))` by decide_tac >>
  qpat_x_assum `fuel-inc = _` (fn th => rewrite_tac[th]) >> gvs[] >>
  qexists_tac `extra ++ FLAT sitess` >> simp[]
QED

Finalise dft_packet_closed_rows_source


Theorem dft_packet_closed_rows_activation:
  !N C7 C8 sf tf a inc ir out bbs bts entries mss ess kss.
    0 < LENGTH bbs /\ inc + LENGTH bbs <= N /\
    LENGTH bts = LENGTH bbs /\ LENGTH entries = LENGTH bbs /\
    LENGTH mss = LENGTH bbs /\ LENGTH ess = LENGTH bbs /\
    LENGTH kss = LENGTH bbs /\
    (!i. i < LENGTH bbs ==>
      lookup_block (EL i entries).vs_current_bb sf.fn_blocks = SOME (EL i bbs) /\
      lookup_block (EL i entries).vs_current_bb tf.fn_blocks = SOME (EL i bts) /\
      (SUC i < LENGTH bbs ==> ~(EL (SUC i) entries).vs_halted) /\
      EVERY IS_SOME (EL i mss) /\
      LENGTH (EL i mss) = LENGTH (EL i ess) /\
      LENGTH (EL i mss) = LENGTH (EL i kss) /\
      PERM (MAP THE (EL i mss) ++
        (if SUC i < LENGTH bbs then (EL (SUC i) entries).vs_gas_readings
         else out.vs_gas_readings)) (EL i entries).vs_gas_readings /\
      (?sp. eval_phis (EL i entries) (EL i bbs).bb_instructions = OK sp /\
        !F. N <= F ==>
          run_block (F-(inc+SUC i)) C8 (EL i bts) (EL i entries) =
            (if SUC i < LENGTH bbs then OK (EL (SUC i) entries)
             else IntRet ir out) /\
          (!gs tail.
            LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL i mss) gs ==>
            (?extra. EL i ess =
              gas_events_block (F-(inc+SUC i)) C7 sf.fn_name (EL i bbs)
                (sp with <|vs_gas_readings := gs ++ tail;
                  vs_inst_idx := phi_prefix_length (EL i bbs).bb_instructions|>) ++ extra) /\
            ((?f. terminates (run_block f C7 (EL i bbs)
                (EL i entries with vs_gas_readings := gs ++ tail))) ==>
              terminates (run_block (F-(inc+SUC i)) C7 (EL i bbs)
                (EL i entries with vs_gas_readings := gs ++ tail)) /\
              dft_res_rel
                (restore_result [] (run_block (F-(inc+SUC i)) C7 (EL i bbs)
                  (EL i entries with vs_gas_readings := gs ++ tail)))
                (restore_result [] (if SUC i < LENGTH bbs then OK (EL (SUC i) entries)
                  else IntRet ir out)) /\
              residual_result tail
                (if SUC i < LENGTH bbs then OK (EL (SUC i) entries) else IntRet ir out)
                (run_block (F-(inc+SUC i)) C7 (EL i bbs)
                  (EL i entries with vs_gas_readings := gs ++ tail)) /\
              gas_events_block (F-(inc+SUC i)) C7 sf.fn_name (EL i bbs)
                (sp with <|vs_gas_readings := gs ++ tail;
                  vs_inst_idx := phi_prefix_length (EL i bbs).bb_instructions|>) = EL i ess) /\
            (!v. (run_block (F-(inc+SUC i)) C7 (EL i bbs)
                    (EL i entries with vs_gas_readings := gs ++ tail) = OK v \/
                  ?ret. run_block (F-(inc+SUC i)) C7 (EL i bbs)
                    (EL i entries with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
              trace_gas (trace_block a (inc+SUC i) (F-(inc+SUC i)) C7 sf (EL i bbs)
                (sp with <|vs_gas_readings := gs ++ tail;
                  vs_inst_idx := phi_prefix_length (EL i bbs).bb_instructions|>)) =
                  ZIP (EL i kss,gs))))) ==>
    EVERY IS_SOME (FLAT mss) /\
    LENGTH (FLAT mss) = LENGTH (FLAT ess) /\
    LENGTH (FLAT mss) = LENGTH (FLAT kss) /\
    PERM (MAP THE (FLAT mss) ++ out.vs_gas_readings) (HD entries).vs_gas_readings /\
    (!F. N <= F ==>
      run_blocks (F-inc) C8 tf (HD entries) = IntRet ir out /\
      !gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT mss) gs ==>
        (?extra. FLAT ess = gas_events_blocks (F-inc) C7 sf
          (HD entries with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (run_blocks f C7 sf
            (HD entries with vs_gas_readings := gs ++ tail))) ==>
          terminates (run_blocks (F-inc) C7 sf
            (HD entries with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (run_blocks (F-inc) C7 sf
              (HD entries with vs_gas_readings := gs ++ tail)))
            (restore_result [] (IntRet ir out)) /\
          residual_result tail (IntRet ir out) (run_blocks (F-inc) C7 sf
            (HD entries with vs_gas_readings := gs ++ tail)) /\
          gas_events_blocks (F-inc) C7 sf
            (HD entries with vs_gas_readings := gs ++ tail) = FLAT ess) /\
        (!v. (run_blocks (F-inc) C7 sf
                (HD entries with vs_gas_readings := gs ++ tail) = OK v \/
              ?ret. run_blocks (F-inc) C7 sf
                (HD entries with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
          trace_gas (trace_blocks a inc (F-inc) C7 sf
            (HD entries with vs_gas_readings := gs ++ tail)) = ZIP (FLAT kss,gs)))
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY IS_SOME (FLAT mss) /\
   LENGTH (FLAT mss) = LENGTH (FLAT ess) /\
   LENGTH (FLAT mss) = LENGTH (FLAT kss) /\
   PERM (MAP THE (FLAT mss) ++ out.vs_gas_readings) (HD entries).vs_gas_readings` by
    suspend "conservation" >>
  simp[] >> qx_gen_tac `fuel` >> strip_tac >> conj_tac
  >- suspend "target" >>
  suspend "source"
QED

Resume dft_packet_closed_rows_activation[conservation]:
  irule dft_packet_closed_rows_conservation >> simp[] >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH bbs ==> _` (qspec_then `i` mp_tac) >> simp[]
QED

Resume dft_packet_closed_rows_activation[target]:
  irule (Q.ISPEC `bbs:basic_block list` dft_packet_closed_rows_target) >>
  qexistsl_tac [`N`,`bbs`,`bts`] >> simp[] >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH bbs ==> _` (qspec_then `i` mp_tac) >> simp[] >>
  metis_tac[]
QED

Resume dft_packet_closed_rows_activation[source]:
  `!gs tail.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT mss) gs ==>
    LENGTH (FLAT kss) = LENGTH gs /\
    (?extra. FLAT ess = gas_events_blocks (fuel-inc) C7 sf
      (HD entries with vs_gas_readings := gs ++ tail) ++ extra) /\
    ((?f. terminates (run_blocks f C7 sf
        (HD entries with vs_gas_readings := gs ++ tail))) ==>
      run_blocks (fuel-inc) C7 sf (HD entries with vs_gas_readings := gs ++ tail) =
        IntRet ir (out with vs_gas_readings := tail) /\
      gas_events_blocks (fuel-inc) C7 sf
        (HD entries with vs_gas_readings := gs ++ tail) = FLAT ess) /\
    (!v. (run_blocks (fuel-inc) C7 sf
            (HD entries with vs_gas_readings := gs ++ tail) = OK v \/
          ?ret. run_blocks (fuel-inc) C7 sf
            (HD entries with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
      trace_gas (trace_blocks a inc (fuel-inc) C7 sf
        (HD entries with vs_gas_readings := gs ++ tail)) = ZIP (FLAT kss,gs))` by
    suspend "source_contract" >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`gs`,`tail`] mp_tac) >> simp[] >> strip_tac >> simp[] >>
  strip_tac >> gvs[] >>
  simp[terminates_def, dft_packet_residual_intret,
    dftGasFromListRestoreTheory.restore_result_def]
QED

Resume dft_packet_closed_rows_activation[source_contract]:
  rpt gen_tac >> strip_tac >>
  irule dft_packet_closed_rows_source >> qexistsl_tac [`N`,`bbs`,`mss`] >> simp[] >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH bbs ==> _` (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >> simp[] >> metis_tac[]
QED

Finalise dft_packet_closed_rows_activation
