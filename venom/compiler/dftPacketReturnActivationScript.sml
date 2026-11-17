Theory dftPacketReturnActivation
Ancestors
  dftPacketClosedRows dftPacketClosedRowNative dftPacketEntryReplay
  dftGasPrefixProvider dftGasToListReplay dftIndexedExec dftGasFromListTraceDefs
  gasEvents frameGasEvents venomExecSemantics venomExecProofs venomInst venomState
  stateEquiv list rich_list arithmetic finite_map dftGasFromListRestore sorting passSimulationDefs

Theorem return_pseudo_events[local]:
  !pre bb s t.
    EVERY (\i. is_pseudo i.inst_opcode) pre /\
    DROP s.vs_inst_idx bb.bb_instructions = pre ++ rest /\
    FOLDR (dft_exec_cons f C) OK pre s = OK t ==>
    gas_events_block f C owner bb s = gas_events_block f C owner bb t
Proof
  Induct_on `pre` >- simp[] >> rpt gen_tac >> strip_tac >>
  `h.inst_opcode <> INVOKE /\ h.inst_opcode <> GAS /\
   ~is_terminator h.inst_opcode` by
    (Cases_on `h.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[LIST_EQ_REWRITE,LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre ++ rest` by
    gvs[DROP_CONS_EL] >>
  `get_instruction bb s.vs_inst_idx = SOME h` by simp[get_instruction_def] >>
  gvs[dft_exec_cons_def,AllCaseEqs()] >>
  rename1 `step_inst f C h s = OK u` >>
  simp[Once gas_events_defs,get_instruction_def,gas_events_step_plain] >>
  first_x_assum irule >> simp[]
QED

Theorem dft_packet_return_closed_row_boundary:
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  eval_phis entry ps = OK sp /\
  FOLDR (dft_exec_cons g D) OK (DROP (phi_prefix_length ps) ps)
    (sp with vs_inst_idx := phi_prefix_length ps) = OK be /\
  be.vs_inst_idx = LENGTH ps /\
  xs <> [] /\ is_terminator (LAST xs).inst_opcode ==>
  be.vs_gas_readings = entry.vs_gas_readings /\
  eval_phis entry bb.bb_instructions = OK sp /\
  !f C ws a e sf.
    run_block f C bb (entry with vs_gas_readings := ws) =
      FOLDR (dft_exec_cons f C) OK xs (be with vs_gas_readings := ws) /\
    gas_events_block f C sf.fn_name bb
      (sp with <|vs_gas_readings := ws; vs_inst_idx := phi_prefix_length bb.bb_instructions|>) =
      gas_events_block f C sf.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
        (be with vs_gas_readings := ws) /\
    trace_gas (trace_block a e f C sf bb
      (sp with <|vs_gas_readings := ws; vs_inst_idx := phi_prefix_length bb.bb_instructions|>)) =
      trace_gas (trace_block a e f C sf
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
        (be with vs_gas_readings := ws))
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs` by
    (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `phi_prefix_length ps <= LENGTH ps` by simp[phi_prefix_length_le] >>
  drule_all native_pseudo_phase_readings >> strip_tac >>
  simp[dft_eval_phis_append,dft_phi_prefix_append] >>
  rpt gen_tac >>
  `FOLDR (dft_exec_cons f C) OK (DROP (phi_prefix_length ps) ps)
    ((sp with vs_gas_readings := ws) with vs_inst_idx := phi_prefix_length ps) =
    OK (be with vs_gas_readings := ws)` by simp[] >>
  qabbrev_tac `start = (sp with vs_gas_readings := ws) with vs_inst_idx := phi_prefix_length ps` >>
  qabbrev_tac `bs = be with vs_gas_readings := ws` >>
  `DROP start.vs_inst_idx bb.bb_instructions = DROP (phi_prefix_length ps) ps ++ xs /\
   TAKE (LENGTH ps - phi_prefix_length ps) (DROP start.vs_inst_idx bb.bb_instructions) =
     DROP (phi_prefix_length ps) ps` by
    simp[Abbr `start`,DROP_APPEND1,phi_prefix_length_le,TAKE_APPEND,LENGTH_DROP] >>
  conj_tac
  >- (simp[run_block_def,dft_eval_phis_append,dft_phi_prefix_append] >>
      irule EQ_TRANS >> qexists `exec_block f C bb bs` >> conj_tac
      >- (irule native_exec_block_prefix_skip >>
          qexists `LENGTH ps - phi_prefix_length ps` >>
          simp[Abbr `start`,phi_prefix_length_le] >>
          irule EVERY_MONOTONIC >> qexists `\i. is_pseudo i.inst_opcode` >>
          simp[EVERY_DROP] >> qx_gen_tac `i` >> Cases_on `i.inst_opcode` >>
          simp[is_pseudo_def,is_terminator_def]) >>
      irule native_exec_block_terminated_fold >>
      simp[Abbr `bs`,DROP_APPEND]) >>
  conj_tac
  >- (irule EQ_TRANS >> qexists `gas_events_block f C sf.fn_name bb bs` >>
      conj_tac
      >- (irule return_pseudo_events >>
          qexistsl [`DROP (phi_prefix_length ps) ps`,`xs`] >>
          simp[EVERY_DROP,Abbr `start`]) >>
      irule gas_events_block_suffix_cong >> qexists `xs` >>
      simp[Abbr `bs`,DROP_APPEND]) >>
  irule EQ_TRANS >> qexists `trace_gas (trace_block a e f C sf bb bs)` >>
  conj_tac
  >- (irule native_trace_block_pseudo_skip >>
      qexists `LENGTH ps - phi_prefix_length ps` >>
      simp[Abbr `start`,phi_prefix_length_le,EVERY_DROP]) >>
  AP_TERM_TAC >> irule native_trace_block_suffix_cong >>
  simp[Abbr `bs`,DROP_APPEND]
QED

Theorem dft_packet_return_row_certificate:
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  xs <> [] /\ is_terminator (LAST xs).inst_opcode /\
  ys <> [] /\ is_terminator (LAST ys).inst_opcode /\
  eval_phis entry ps = OK sp /\
  FOLDR (dft_exec_cons g D) OK (DROP (phi_prefix_length ps) ps)
    (sp with vs_inst_idx := phi_prefix_length ps) = OK be /\
  be.vs_inst_idx = LENGTH ps /\
  EVERY IS_SOME ms /\ LENGTH ms = LENGTH es /\ LENGTH ms = LENGTH ks /\
  PERM (MAP THE ms ++ rest) be.vs_gas_readings /\
  (!F. N <= F ==>
    FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
    (!gs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) ms gs ==>
      (?extra. es = gas_events_block (F-e) C7 sf.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
        (be with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
          (be with vs_gas_readings := gs ++ tail))) ==>
        terminates (FOLDR (dft_exec_cons (F-e) C7) OK xs
          (be with vs_gas_readings := gs ++ tail)) /\
        dft_res_rel
          (restore_result [] (FOLDR (dft_exec_cons (F-e) C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
        gas_events_block (F-e) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail) = es /\
        residual_result tail r8 (FOLDR (dft_exec_cons (F-e) C7) OK xs
          (be with vs_gas_readings := gs ++ tail))) /\
      (!v. (FOLDR (dft_exec_cons (F-e) C7) OK xs
              (be with vs_gas_readings := gs ++ tail) = OK v \/
            ?ir. FOLDR (dft_exec_cons (F-e) C7) OK xs
              (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
        trace_gas (trace_block a e (F-e) C7 sf
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail)) = ZIP (ks,gs)))) ==>
  EVERY IS_SOME ms /\ LENGTH ms = LENGTH es /\ LENGTH ms = LENGTH ks /\
  PERM (MAP THE ms ++ rest) entry.vs_gas_readings /\
  (?sp. eval_phis entry bb.bb_instructions = OK sp /\
    !F. N <= F ==>
      run_block (F-e) C8 bt entry = r8 /\
      (!gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) ms gs ==>
        (?extra. es = gas_events_block (F-e) C7 sf.fn_name bb
          (sp with <|vs_gas_readings := gs ++ tail;
            vs_inst_idx := phi_prefix_length bb.bb_instructions|>) ++ extra) /\
        ((?f. terminates (run_block f C7 bb (entry with vs_gas_readings := gs ++ tail))) ==>
          terminates (run_block (F-e) C7 bb (entry with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel (restore_result [] (run_block (F-e) C7 bb
            (entry with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
          residual_result tail r8 (run_block (F-e) C7 bb
            (entry with vs_gas_readings := gs ++ tail)) /\
          gas_events_block (F-e) C7 sf.fn_name bb
            (sp with <|vs_gas_readings := gs ++ tail;
              vs_inst_idx := phi_prefix_length bb.bb_instructions|>) = es) /\
        (!v. (run_block (F-e) C7 bb (entry with vs_gas_readings := gs ++ tail) = OK v \/
              ?ret. run_block (F-e) C7 bb (entry with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
          trace_gas (trace_block a e (F-e) C7 sf bb
            (sp with <|vs_gas_readings := gs ++ tail;
              vs_inst_idx := phi_prefix_length bb.bb_instructions|>)) = ZIP (ks,gs))))
Proof
  strip_tac >> (
  qpat_assum `bb.bb_instructions = ps ++ xs`
    (mp_then Any mp_tac dft_packet_return_closed_row_boundary) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  pop_assum (mk_asm "source_bridge") >>
  qpat_assum `bt.bb_instructions = ps ++ ys`
    (mp_then Any mp_tac dft_packet_return_closed_row_boundary) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  pop_assum (mk_asm "target_bridge") >>
  `be with vs_gas_readings := entry.vs_gas_readings = be` by
    gvs[venom_state_component_equality] >>
  simp[] >> (conj_tac >- metis_tac[]) >>
  qx_gen_tac `fuel` >> strip_tac >>
  qpat_x_assum `!F. N <= F ==> _` (qspec_then `fuel` mp_tac) >> simp[] >>
  strip_tac >> conj_tac
  >- (asm "target_bridge"
        (qspecl_then [`fuel-e`,`C8`,`entry.vs_gas_readings`,`a`,`e`,`sf`]
          (assume_tac o cj 1)) >> gvs[]) >>
  map_every qx_gen_tac [`gs`,`tail`] >> disch_tac >>
  asm "source_bridge" (qspecl_then [`fuel-e`,`C7`,`gs ++ tail`,`a`,`e`,`sf`] strip_assume_tac) >>
  qpat_x_assum `!gs tail. _` (qspecl_then [`gs`,`tail`] mp_tac) >>
  asm "source_bridge" (fn th => simp[th]) >> metis_tac[])
QED

Theorem dft_packet_return_closed_activation:
  order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
  LAST order <= N /\
  LENGTH bbs = LENGTH order /\ LENGTH bts = LENGTH order /\
  LENGTH entries = LENGTH order /\ HD entries = entry /\
  mss = MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e)))) order /\
  ess = MAP (\e. FLAT (THE (FLOOKUP es_tab (a,e)))) order /\
  kss = MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e)))) order /\
  (!i. i < LENGTH order ==>
    lookup_block (EL i entries).vs_current_bb sf.fn_blocks = SOME (EL i bbs) /\
    lookup_block (EL i entries).vs_current_bb tf.fn_blocks = SOME (EL i bts) /\
    (SUC i < LENGTH order ==> ~(EL (SUC i) entries).vs_halted) /\
    ?ps xs ys rho h0 be hbe count r8 rest ms es ks sp g D.
      FLOOKUP blocks (a,EL i order) =
        SOME (EL i bbs,EL i bts,ps,xs,ys,rho,EL i entries,h0,
          SOME (be,hbe),count,r8,T,SOME rest) /\
      FLOOKUP ms_tab (a,EL i order) = SOME ms /\
      FLOOKUP es_tab (a,EL i order) = SOME es /\
      FLOOKUP ks_tab (a,EL i order) = SOME ks /\
      (EL i bbs).bb_instructions = ps ++ xs /\
      (EL i bts).bb_instructions = ps ++ ys /\
      EVERY (\x. is_pseudo x.inst_opcode) ps /\
      EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
      EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
      xs <> [] /\ is_terminator (LAST xs).inst_opcode /\
      ys <> [] /\ is_terminator (LAST ys).inst_opcode /\
      eval_phis (EL i entries) ps = OK sp /\
      FOLDR (dft_exec_cons g D) OK (DROP (phi_prefix_length ps) ps)
        (sp with vs_inst_idx := phi_prefix_length ps) = OK be /\
      be.vs_inst_idx = LENGTH ps /\
      r8 = (if SUC i < LENGTH order then OK (EL (SUC i) entries) else IntRet ir out) /\
      rest = (if SUC i < LENGTH order then (EL (SUC i) entries).vs_gas_readings
              else out.vs_gas_readings) /\
      EVERY IS_SOME (FLAT ms) /\
      LENGTH (FLAT ms) = LENGTH (FLAT es) /\ LENGTH (FLAT ms) = LENGTH (FLAT ks) /\
      PERM (MAP THE (FLAT ms) ++ rest) be.vs_gas_readings /\
      (!F. N <= F ==>
        FOLDR (dft_exec_cons (F-EL i order) C8) OK ys be = r8 /\
        (!gs tail.
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
          (?extra. FLAT es = gas_events_block (F-EL i order) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail) ++ extra) /\
          ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
              (be with vs_gas_readings := gs ++ tail))) ==>
            terminates (FOLDR (dft_exec_cons (F-EL i order) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)) /\
            dft_res_rel
              (restore_result [] (FOLDR (dft_exec_cons (F-EL i order) C7) OK xs
                (be with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
            gas_events_block (F-EL i order) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT es /\
            residual_result tail r8 (FOLDR (dft_exec_cons (F-EL i order) C7) OK xs
              (be with vs_gas_readings := gs ++ tail))) /\
          (!v. (FOLDR (dft_exec_cons (F-EL i order) C7) OK xs
                  (be with vs_gas_readings := gs ++ tail) = OK v \/
                ?ret. FOLDR (dft_exec_cons (F-EL i order) C7) OK xs
                  (be with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
            trace_gas (trace_block a (EL i order) (F-EL i order) C7 sf
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs))))) ==>
  terminates (IntRet ir out) /\
  LENGTH (FLAT mss) = LENGTH (FLAT ess) /\
  LENGTH (FLAT mss) = LENGTH (FLAT kss) /\
  PERM (MAP THE (FILTER IS_SOME (FLAT mss)) ++ out.vs_gas_readings) entry.vs_gas_readings /\
  EVERY IS_SOME (FLAT mss) /\
  (!F. N <= F ==>
    run_blocks (F-inc) C8 tf entry = IntRet ir out /\
    (!gs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT mss) gs ==>
      (?extra. FLAT ess = gas_events_blocks (F-inc) C7 sf
        (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?f. terminates (run_blocks f C7 sf
          (entry with vs_gas_readings := gs ++ tail))) ==>
        terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
        dft_res_rel
          (restore_result [] (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)))
          (restore_result [] (IntRet ir out)) /\
        gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = FLAT ess /\
        residual_result tail (IntRet ir out)
          (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail))) /\
      (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
            ?ret. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
        trace_gas (trace_blocks a inc (F-inc) C7 sf
          (entry with vs_gas_readings := gs ++ tail)) = ZIP (FLAT kss,gs))))
Proof
  strip_tac >>
  `0 < LENGTH order /\ inc + LENGTH order <= N` by
    (conj_tac >- (Cases_on `order` >> gvs[]) >>
     qpat_assum `order = GENLIST _ _` (mp_tac o AP_TERM ``LAST:num list -> num``) >>
     Cases_on `LENGTH order` >- gvs[] >>
     gvs[GENLIST_LAST]) >>
  `EVERY IS_SOME (FLAT mss) /\
   LENGTH (FLAT mss) = LENGTH (FLAT ess) /\
   LENGTH (FLAT mss) = LENGTH (FLAT kss) /\
   PERM (MAP THE (FLAT mss) ++ out.vs_gas_readings) entry.vs_gas_readings /\
   (!F. N <= F ==>
     run_blocks (F-inc) C8 tf entry = IntRet ir out /\
     !gs tail.
       LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT mss) gs ==>
       (?extra. FLAT ess = gas_events_blocks (F-inc) C7 sf
         (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
       ((?f. terminates (run_blocks f C7 sf
           (entry with vs_gas_readings := gs ++ tail))) ==>
         terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
         dft_res_rel
           (restore_result [] (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)))
           (restore_result [] (IntRet ir out)) /\
         residual_result tail (IntRet ir out)
           (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
         gas_events_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = FLAT ess) /\
       (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
             ?ret. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ret v) ==>
         trace_gas (trace_blocks a inc (F-inc) C7 sf
           (entry with vs_gas_readings := gs ++ tail)) = ZIP (FLAT kss,gs)))` by
    suspend "compose" >>
  `FILTER IS_SOME (FLAT mss) = FLAT mss` by metis_tac[FILTER_EQ_ID] >>
  simp[terminates_def] >> metis_tac[]
QED

Resume dft_packet_return_closed_activation[compose]:
  qpat_x_assum `HD entries = entry` (fn th => rewrite_tac[GSYM th]) >>
  irule dft_packet_closed_rows_activation >>
  qexistsl [`bbs`,`bts`] >> simp[] >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH order ==> _` (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >>
  `EL i order = inc + SUC i` by
    (qpat_assum `order = GENLIST _ _` (fn th => simp[Once th,EL_GENLIST])) >>
  simp[EL_MAP] >>
  drule_all dft_packet_return_row_certificate >> simp[]
QED

Finalise dft_packet_return_closed_activation
