Theory requestCutPacketPlan
Ancestors
  requestCutClosedPlan requestCutPacketOrder requestCutPacketClosedRow dftFinitePacket
  dftPacketFillingBoundary dftGasFromListTraceDefs dftIndexedExec
  venomExecSemantics venomState list rich_list arithmetic finite_map

Theorem request_cut_packet_predecessor_plan:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a sf tf inc entry order res nrest
    ds e later fuel gss tail slots keys plan row_run.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    order = ds ++ e::later /\ N <= fuel /\ inc + SUC (LENGTH ds) <= fuel /\
    slots = MAP (\f. FLAT (THE (FLOOKUP ms_tab (a,f)))) ds /\
    keys = MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) ds /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) slots gss /\
    plan = MAP (\f. (FST (THE (FLOOKUP blocks (a,f))),f,
      DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
        (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds /\
    row_run = (\(bb,f,z) s. case eval_phis s bb.bb_instructions of
      OK sp => FOLDR (dft_exec_cons (fuel-f) C7) OK z
                    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    | other => other) ==>
    case FOLDL (\r row. case r of OK s => row_run row s | other => other)
        (OK (entry with vs_gas_readings := FLAT gss ++ tail)) plan of
      OK u => u = (case THE (FLOOKUP blocks (a,e)) of
          (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) => inf)
          with vs_gas_readings := tail /\
        run_blocks (fuel-inc) C7 sf (entry with vs_gas_readings := FLAT gss ++ tail) =
          run_blocks (fuel-inc-LENGTH ds) C7 sf u /\
        MAP FST (trace_gas (trace_blocks a inc (fuel-inc) C7 sf
          (entry with vs_gas_readings := FLAT gss ++ tail))) =
            FLAT keys ++ MAP FST (trace_gas
              (trace_blocks a (inc + LENGTH ds) (fuel-inc-LENGTH ds) C7 sf u))
    | stopped => ~(?ir u. stopped = IntRet ir u) /\
        run_blocks (fuel-inc) C7 sf (entry with vs_gas_readings := FLAT gss ++ tail) = stopped /\
        ?extra. FLAT keys = MAP FST (trace_gas (trace_blocks a inc (fuel-inc) C7 sf
          (entry with vs_gas_readings := FLAT gss ++ tail))) ++ extra
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `start = entry with vs_gas_readings := FLAT gss ++ tail` >>
  qabbrev_tac `input_at = (\i. case THE (FLOOKUP blocks (a, EL i order)) of
    (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) => inf)` >>
  qabbrev_tac `P = (\i s. s = input_at i with vs_gas_readings := FLAT (DROP i gss) ++ tail)` >>
  qabbrev_tac `run_at = (\i s. (run_blocks (fuel-inc-i) C7 sf s,
    MAP FST (trace_gas (trace_blocks a (inc+i) (fuel-inc-i) C7 sf s))))` >>
  `LENGTH keys = LENGTH plan /\ LENGTH gss = LENGTH ds` by
    metis_tac[LENGTH_MAP, LIST_REL_LENGTH] >>
  `P 0 start` by suspend "first_input" >>
  `!i s. i < LENGTH (MAP row_run plan) /\ P i s ==>
    case EL i (MAP row_run plan) s of
      OK t => P (SUC i) t /\ FST (run_at i s) = FST (run_at (SUC i) t) /\
        SND (run_at i s) = EL i keys ++ SND (run_at (SUC i) t)
    | stopped => ~(?ir u. stopped = IntRet ir u) /\ FST (run_at i s) = stopped /\
        ?extra. EL i keys = SND (run_at i s) ++ extra` by suspend "row" >>
  mp_tac (Q.SPECL [`MAP row_run (plan : (basic_block # num # instruction list) list)`,`keys`,`start`,`P`,`run_at`]
    request_cut_plan_keys) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_assum `LENGTH keys = LENGTH plan` (fn th => simp[NoAsms,LENGTH_MAP,th])) >>
  simp_tac bool_ss [FOLDL_MAP] >>
  simp[NoAsms, Abbr `run_at`] >>
  BasicProvers.TOP_CASE_TAC >> simp[NoAsms] >>
  simp[Abbr `P`, Abbr `input_at`, EL_APPEND_EQN, DROP_LENGTH_TOO_LONG, Abbr `start`]
QED

Resume request_cut_packet_predecessor_plan[first_input]:
  Cases_on `ds`
  >- suspend "first_is_active" >>
  `SUC 0 < LENGTH order` by simp[] >>
  drule_all request_cut_packet_predecessor >> simp[EL] >>
  strip_tac >>
  simp[Abbr `P`,Abbr `input_at`,Abbr `start`] >>
  gvs[]
QED

Resume request_cut_packet_predecessor_plan[first_is_active]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
    (fn info => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
      (strip_assume_tac o MATCH_MP info)) >>
  `e = SUC inc /\ (a,e) IN FDOM blocks` by
    (qpat_assum `order = [] ++ e::later` mp_tac >>
     qpat_assum `order = GENLIST _ _` mp_tac >>
     qpat_assum `!e. MEM e order <=> (a,e) IN FDOM blocks` (qspec_then `e` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> gvs[] >>
     qpat_assum `e::later = GENLIST _ _` (mp_tac o AP_TERM ``HD:num list -> num``) >>
     simp[HD_GENLIST]) >>
  `?row. FLOOKUP blocks (a,e) = SOME row` by
    (qpat_assum `(a,e) IN FDOM blocks` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
  PairCases_on `row` >>
  qpat_assum `!a e bb bt ps xs ys rho in_state h0 bentry count front closed resti.
    FLOOKUP blocks (a,e) = _ ==> _`
    (fn info => qpat_assum `FLOOKUP blocks (a,e) = SOME _`
      (strip_assume_tac o MATCH_MP info)) >>
  qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
    (fn th => qpat_x_assum `FLOOKUP acts a = SOME _`
      (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o
       REWRITE_RULE [th,optionTheory.SOME_11,pairTheory.PAIR_EQ])) >>
  `row6 = entry` by
    (qpat_assum `e = SUC inc` (fn eq =>
      qpat_assum `if e = SUC inc then row6 = entry else _`
        (ACCEPT_TAC o REWRITE_RULE [eq,COND_CLAUSES]))) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`row6 = entry`,`order = [] ++ e::later`,
     `FLOOKUP blocks (a,e) = SOME (row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12)`,
     `Abbrev (P = _)`,`Abbrev (input_at = _)`,`Abbrev (start = _)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  simp[Abbr `P`,Abbr `input_at`,Abbr `start`]
QED

Resume request_cut_packet_predecessor_plan[row]:
  rpt gen_tac >> strip_tac >>
  `i < LENGTH ds /\ SUC i < LENGTH order` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`order = ds ++ e::later`,`plan = MAP _ ds`,`i < LENGTH (MAP row_run plan)`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[LENGTH_MAP] >> decide_tac) >>
  drule_all request_cut_packet_predecessor >> strip_tac >>
  `EL i ds = EL i order` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`order = ds ++ e::later`,`i < LENGTH ds`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> simp[EL_APPEND_EQN]) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) (EL i gss)` by
    (qpat_assum `LIST_REL (LIST_REL _) slots gss`
      (fn th => qspec_then `i` mp_tac
        (CONJUNCT2 (REWRITE_RULE [LIST_REL_EL_EQN] th))) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`i < LENGTH ds`,`slots = MAP _ ds`,`EL i ds = EL i order`,
        `FLOOKUP ms_tab (a,EL i order) = SOME ms`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[EL_MAP,LIST_REL_EL_EQN]) >>
  `s = hin with vs_gas_readings :=
      EL i gss ++ (FLAT (DROP (SUC i) gss) ++ tail)` by
    (qpat_assum `P i s` mp_tac >>
     qpat_assum `Abbrev (P = _)` (fn th =>
       simp_tac bool_ss [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     qpat_assum `Abbrev (input_at = _)` (fn th =>
       simp_tac bool_ss [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`FLOOKUP blocks (a,EL i order) = SOME _`,`LENGTH gss = LENGTH ds`,`i < LENGTH ds`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[DROP_CONS_EL, APPEND_ASSOC]) >>
  suspend "closed"
QED

Resume request_cut_packet_predecessor_plan[closed]:
  qpat_x_assum `order = ds ++ e::later` (K all_tac) >>
  `0 < EL i order` by simp[] >>
  mp_tac (Q.SPECL
    [`N`,`C7`,`C8`,`root_sf`,`root_tf`,`root_entry`,`packet`,`acts`,`blocks`,`calls`,
     `ms_tab`,`es_tab`,`ks_tab`,`rooted_eval`,`p`,`d`,`q8`,`raw_slots`,`sites`,`unused`,
     `a`,`EL i order`,`sf`,`tf`,`inc`,`entry`,`order`,`res`,`nrest`,
     `bb`,`bt`,`ps`,`xs`,`ys`,`row_order`,`hin`,`h0`,`be`,`hbe`,`count'`,`post`,`rest`,
     `ms`,`ks`,`fuel`,`EL i gss`,`FLAT (DROP (SUC i) gss) ++ tail`]
    request_cut_packet_closed_row_keys) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  `SUC (fuel - EL i order) = fuel-inc-i` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`EL i order = _`,`inc + SUC (LENGTH ds) <= fuel`,`i < LENGTH ds`] >> decide_tac) >>
  `EL i (MAP row_run plan) s = exec_block (fuel-EL i order) C7 bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    suspend "literal_eval" >>
  `EL i keys = FLAT ks` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`keys = MAP _ ds`,`i < LENGTH ds`,`EL i ds = EL i order`,
       `FLOOKUP ks_tab (a,EL i order) = SOME ks`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[EL_MAP]) >>
  `fuel-EL i order = fuel-inc-SUC i /\ EL i order-1 = inc+i /\ EL i order = inc+SUC i` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`EL i order = _`,`inc + SUC (LENGTH ds) <= fuel`,`i < LENGTH ds`] >> decide_tac) >>
  qpat_assum `EL i (MAP row_run plan) s = _` (fn th => rewrite_tac[th]) >>
  Cases_on `exec_block (fuel-EL i order) C7 bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  qpat_assum `EL i order = inc + SUC i` (fn th =>
    gvs[Abbr `run_at`, Abbr `P`, Abbr `input_at`] >>
    simp[NoAsms,th])
QED

Resume request_cut_packet_predecessor_plan[literal_eval]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`plan = MAP _ ds`,`i < LENGTH ds`,`EL i ds = EL i order`,
     `row_run = _`,`FLOOKUP blocks (a,EL i order) = SOME _`,
     `s = hin with vs_gas_readings := _`,
     `eval_phis (hin with vs_gas_readings := _) bb.bb_instructions = OK sp`,
     `FOLDR _ OK _ _ = exec_block _ _ _ _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[EL_MAP]
QED

Finalise request_cut_packet_predecessor_plan
