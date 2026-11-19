Theory requestCutPacketSelectedKeys
Ancestors
  requestCutPacketRootKeys requestCutPacketLevel requestCutPacketLevelOrder
  requestCutPacketFillings requestCutPacketLevelCall
  dftFinitePacket dftGasFromListTraceDefs dftIndexedExec
  venomExecSemantics venomState gasEvents list rich_list arithmetic finite_map

(* The selected cut's inventory extends the actual C7 GAS key trace
   even when a predecessor or active row stops on this filling. *)
Theorem request_cut_packet_selected_keys:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  paths = MAP (\(ai,ds,ei,qi,zi). ai) cuts /\
  paths = REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cuts = LENGTH levels /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
       ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then
        (IS_SOME bei /\ qi <= LENGTH xsi /\
         zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
         EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
         (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r (TAKE counti rhoi))) \/
        (bei = NONE /\ qi = 0 /\
         (!gs. ?sp u. eval_phis (ini with vs_gas_readings := gs) bbi.bb_instructions = OK sp /\
           FOLDR (dft_exec_cons (fuel-ei) C7) OK zi
             (sp with vs_inst_idx := phi_prefix_length bbi.bb_instructions) = OK u))
      else
        ?cid h b0 done_at_call child_entry ret.
          EL (SUC i) paths = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
      EL i levels =
        (sfi,MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++ [(bbi,ei,zi)],
         if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
  Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
  N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  SND (rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = r /\
  ~(?u. r = OK u) ==>
  ~(?ir u. r = IntRet ir u) /\
  run_blocks fuel C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = r /\
  ?extra. Kcut = MAP FST (trace_gas (trace_blocks [] 0 fuel C7 root_sf
    (root_entry with vs_gas_readings := gs ++ tail))) ++ extra
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `slot_pre = (\(ai,ds,ei,qi,zi).
    MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) :
    ((num # num) list # num list # num # num # instruction list) -> bytes32 option list list` >>
  qabbrev_tac `slot_tail = (\(ai,ds,ei,qi,zi). TAKE qi (THE (FLOOKUP ms_tab (ai,ei)))) :
    ((num # num) list # num list # num # num # instruction list) -> bytes32 option list list` >>
  `Mcut = FLAT (MAP (\c. FLAT (slot_pre c) ++ FLAT (slot_tail c)) cuts)` by
    (qpat_assum `Mcut = _` (fn th => once_rewrite_tac[th]) >>
     AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
     once_rewrite_tac[FUN_EQ_THM] >> qx_gen_tac `c` >> PairCases_on `c` >>
     simp[NoAsms,Abbr `slot_pre`,Abbr `slot_tail`]) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
     (FLAT (MAP (\c. FLAT (slot_pre c) ++ FLAT (slot_tail c)) cuts)) gs` by
    metis_tac[] >>
  drule request_cut_packet_level_fillings >> strip_tac >>
  qabbrev_tac `keyss = MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts` >>
  qabbrev_tac `depths = MAP (\path. case path of [] => 0 | (depth,cid)::parent => depth) paths` >>
  qabbrev_tac `entry = root_entry with vs_gas_readings := gs ++ tail` >>
  qabbrev_tac `P = (\i s. i < LENGTH cuts ==>
    ?tf inc ent order res rest.
      FLOOKUP acts (EL i paths) = SOME (FST (EL i levels),tf,inc,ent,order,res,rest) /\
      s = ent with vs_gas_readings := FLAT (DROP i gcs) ++ tail)` >>
  qabbrev_tac `row_run = (\(bb,e,z) s. case eval_phis s bb.bb_instructions of
    OK sp => FOLDR (dft_exec_cons (fuel-e) C7) OK z
                (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
  | other => other)` >>
  qabbrev_tac `level_run = (\((sf:ir_function),plan,call) ent.
    case FOLDL (\v row. case v of OK s => row_run row s | other => other) (OK ent) plan of
      OK caller => (case call of NONE => OK caller | SOME c =>
        (case decode_invoke c of
          NONE => Error "invoke: bad operand format"
        | SOME (nm,ops) =>
          (case lookup_function nm C7.ctx_functions of
            NONE => Error "invoke: function not found"
          | SOME callee =>
            (case eval_operands ops caller of
              NONE => Error "invoke: undefined argument"
            | SOME args =>
              (case setup_callee callee args caller of
                NONE => Error "invoke: empty function" | SOME cs => OK cs)))))
    | other => other)` >>
  qabbrev_tac `run_at = (\i s. if i < LENGTH levels then
    (run_blocks (fuel - EL i depths) C7 (FST (EL i levels)) s,
     MAP FST (trace_gas (trace_blocks (EL i paths) (EL i depths)
       (fuel - EL i depths) C7 (FST (EL i levels)) s)))
    else (OK s,[]))` >>
  `LENGTH paths = LENGTH cuts` by
    (qpat_assum `paths = MAP _ cuts` (fn th => simp[NoAsms,th])) >>
  `paths <> [] /\ HD paths = []` by
    (qpat_assum `paths = REVERSE (GENLIST _ _)`
      (fn th => simp[NoAsms,th,HD_REVERSE,GENLIST_LAST,GENLIST_EQ_NIL])) >>
  `HD depths = 0` by
    (qpat_assum `Abbrev (depths = _)` (fn th =>
       pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     qpat_assum `paths <> []` mp_tac >>
     qpat_assum `HD paths = []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `paths` >> simp[]) >>
  `LENGTH paths = LENGTH levels` by metis_tac[] >>
  `FST (HD levels) = root_sf` by suspend "root_owner" >>
  `P 0 entry` by suspend "initial" >>
  `!i s. i < LENGTH levels /\ P i s ==>
    case level_run (EL i levels) s of
      OK t => P (SUC i) t /\
        (~(?u. FST (run_at (SUC i) t) = OK u) /\
         ~(?ir u. FST (run_at (SUC i) t) = IntRet ir u) ==>
         FST (run_at i s) = FST (run_at (SUC i) t) /\
         SND (run_at i s) = EL i keyss ++ SND (run_at (SUC i) t))
    | stopped => ~(?ir u. stopped = IntRet ir u) /\
        FST (run_at i s) = stopped /\ ?extra. EL i keyss = SND (run_at i s) ++ extra` by
    suspend "visit" >>
  `Kcut = FLAT keyss` by simp[Abbr `keyss`] >>
  `LENGTH keyss = LENGTH levels` by simp[Abbr `keyss`] >>
  `SND (rooted_eval fuel C7 levels entry) = r` by simp[Abbr `entry`] >>
  mp_tac (Q.INST [`P` |-> `P`, `run_at` |-> `run_at`, `keyss` |-> `keyss`,
    `entry` |-> `entry`, `row_run` |-> `row_run`, `level_run` |-> `level_run`]
    request_cut_packet_root_keys) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[GSYM markerTheory.Abbrev_def]) >>
  qpat_assum `Kcut = FLAT keyss` (fn th => simp[NoAsms,th,Abbr `entry`])
QED

Resume request_cut_packet_selected_keys[root_owner]:
  `0 < LENGTH cuts /\ cuts <> [] /\ levels <> []` by
    (qpat_assum `paths <> []` mp_tac >>
     qpat_assum `LENGTH paths = LENGTH cuts` mp_tac >>
     qpat_assum `LENGTH cuts = LENGTH levels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `cuts` >> Cases_on `levels` >>
     Cases_on `paths` >> simp[]) >>
  qabbrev_tac `cut = EL 0 cuts` >> PairCases_on `cut` >>
  `EL 0 cuts = (cut0,cut1,cut2,cut3,cut4)` by metis_tac[Abbr `cut`] >>
  `cut0 = []` by
    (`EL 0 paths = cut0` by
       (qpat_assum `paths = MAP _ cuts` (fn th => once_rewrite_tac[th]) >>
        qpat_assum `0 < LENGTH cuts` (fn th => asm_simp_tac bool_ss [th,EL_MAP]) >>
        simp[NoAsms]) >>
     qpat_assum `EL 0 paths = cut0` mp_tac >>
     qpat_assum `paths <> []` mp_tac >>
     qpat_assum `HD paths = []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `paths` >> simp[]) >>
  drule request_cut_packet_root_activation >> strip_tac >>
  qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,_,NONE,NONE)`,
     `FLOOKUP acts cut0 = SOME _`,`cut0 = []`,`EL 0 levels = _`,`levels <> []`] >>
  POP_ASSUM_LIST (K all_tac) >> Cases_on `levels` >> simp[] >> metis_tac[]
QED

Resume request_cut_packet_selected_keys[initial]:
  drule request_cut_packet_root_activation >> strip_tac >>
  `EL 0 paths = []` by
    (qpat_assum `HD paths = []` mp_tac >>
     qpat_assum `paths <> []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `paths` >> simp[]) >>
  `FST (EL 0 levels) = root_sf` by
    (qpat_assum `FST (HD levels) = root_sf` mp_tac >>
     qpat_assum `LENGTH paths = LENGTH levels` mp_tac >>
     qpat_assum `paths <> []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `paths` >> Cases_on `levels` >> simp[]) >>
  simp_tac bool_ss [Abbr `P`,Abbr `entry`,DROP_0] >>
  strip_tac >> qexistsl_tac [`root_tf`,`0`,`root_entry`,`order`,`NONE`,`NONE`] >>
  metis_tac[]
QED

Resume request_cut_packet_selected_keys[visit]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `i < LENGTH cuts /\ i < LENGTH paths /\ i < LENGTH gcs` by
    metis_tac[] >>
  qabbrev_tac `cut = EL i cuts` >> PairCases_on `cut` >>
  `EL i cuts = (cut0,cut1,cut2,cut3,cut4)` by metis_tac[Abbr `cut`] >>
  qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!i. i < LENGTH cuts ==> ?gps gas. _`
    (drule_then strip_assume_tac) >>
  `EL i paths = cut0` by
    (qpat_assum `paths = MAP _ cuts` (fn th => once_rewrite_tac[th]) >>
     asm_simp_tac bool_ss [EL_MAP,pairTheory.UNCURRY_DEF]) >>
  `EL i depths = (case cut0 of [] => 0 | (depth,cid)::parent => depth)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`EL i paths = cut0`,`i < LENGTH paths`,`Abbrev (depths = _)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def,EL_MAP]) >>
  Q.SUBGOAL_THEN `cut2 = inci + SUC (LENGTH cut1) /\ cut2 <= N /\ inci = EL i depths /\
    (?ms. FLOOKUP ms_tab (cut0,cut2) = SOME ms) /\
    (?ks. FLOOKUP ks_tab (cut0,cut2) = SOME ks)` ASSUME_TAC >-
    (drule_all request_cut_packet_level_position >>
     qpat_assum `EL i depths = _` (fn th => simp[NoAsms,th])) >>
  qpat_x_assum `_ /\ _ /\ _ /\ (?ms. _) /\ (?ks. _)` strip_assume_tac >>
  `s = enti with vs_gas_readings := FLAT gps ++ FLAT gas ++
      (FLAT (DROP (SUC i) gcs) ++ tail)` by suspend "level_input" >>
  qabbrev_tac `rest = FLAT (DROP (SUC i) gcs) ++ tail` >>
  qabbrev_tac `prev = MAP (\f. (FST (THE (FLOOKUP blocks (cut0,f))),f,
    DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (cut0,f)))).bb_instructions)
      (FST (THE (FLOOKUP blocks (cut0,f)))).bb_instructions)) cut1` >>
  qabbrev_tac `prev_keys = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (cut0,f)))) cut1)` >>
  qabbrev_tac `active_keys = FLAT (TAKE cut3 ks)` >>
  `EL i keyss = prev_keys ++ active_keys` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`FLOOKUP ks_tab (cut0,cut2) = SOME ks`,`EL i cuts = _`,`i < LENGTH cuts`] >>
     simp[NoAsms,Abbr `keyss`,Abbr `prev_keys`,Abbr `active_keys`,EL_MAP]) >>
  `LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
     (MAP (\f. FLAT (THE (FLOOKUP ms_tab (cut0,f)))) cut1) gps /\
   LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE cut3 ms) gas` by
    (qpat_assum `LIST_REL (LIST_REL _) (slot_pre _) _` mp_tac >>
     qpat_assum `LIST_REL (LIST_REL _) (slot_tail _) _` mp_tac >>
     qpat_assum `EL i cuts = _` mp_tac >>
     qpat_assum `FLOOKUP ms_tab (cut0,cut2) = SOME ms` mp_tac >>
     simp[NoAsms,Abbr `slot_pre`,Abbr `slot_tail`]) >>
  qabbrev_tac `partial = FOLDL (\r row. case r of OK st => row_run row st | other => other)
                    (OK s) (prev ++ [(bbi,cut2,cut4)])` >>
  `level_run (EL i levels) s =
    case partial of
      OK caller => (if SUC i = LENGTH cuts then OK caller else
        (case decode_invoke (EL cut3 xsi) of
          NONE => Error "invoke: bad operand format"
        | SOME (nm,ops) =>
          (case lookup_function nm C7.ctx_functions of
            NONE => Error "invoke: function not found"
          | SOME callee =>
            (case eval_operands ops caller of
              NONE => Error "invoke: undefined argument"
            | SOME args =>
              (case setup_callee callee args caller of
                NONE => Error "invoke: empty function" | SOME cs => OK cs)))))
    | stopped => stopped` by
    (Cases_on `SUC i = LENGTH cuts` >>
     simp[Abbr `level_run`,Abbr `partial`,Abbr `prev`]) >>
  qpat_assum `level_run (EL i levels) s = _` (fn th => rewrite_tac[th]) >>
  `FST (run_at i s) = run_blocks (fuel-inci) C7 sfi s /\
   SND (run_at i s) = MAP FST (trace_gas (trace_blocks cut0 inci (fuel-inci) C7 sfi s))` by
    simp[Abbr `run_at`] >>
  `!be hbe. bei = SOME (be,hbe) /\ cut3 <= LENGTH xsi /\
    cut4 = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE cut3 xsi /\
    EVERY (\x. ~is_terminator x.inst_opcode) (TAKE cut3 xsi) /\
    (!q. q < cut3 /\ (EL q xsi).inst_opcode = INVOKE ==> MEM q (TAKE counti rhoi)) ==>
    case partial of
      OK u => u.vs_inst_idx = LENGTH psi + cut3 /\ u.vs_gas_readings = rest /\
        FOLDR (dft_exec_cons (fuel-cut2) C7) OK (TAKE cut3 xsi)
          (be with vs_gas_readings := FLAT gas ++ rest) = OK u /\
        (!r. exec_block (fuel-cut2) C7 bbi u = r /\ ~(?v. r = OK v) ==>
          FST (run_at i s) = r /\
          SND (run_at i s) = EL i keyss ++ MAP FST
            (trace_gas (trace_block cut0 cut2 (fuel-cut2) C7 sfi bbi u)))
    | stopped => ~(?ir u. stopped = IntRet ir u) /\
        FST (run_at i s) = stopped /\ ?extra. EL i keyss = SND (run_at i s) ++ extra` by
    suspend "body_fact" >>
  Cases_on `SUC i = LENGTH cuts`
  >- suspend "last_visit" >>
  suspend "caller_visit"
QED

Resume request_cut_packet_selected_keys[level_input]:
  qpat_assum `P i s` mp_tac >>
  qpat_assum `FLOOKUP acts cut0 = SOME _` mp_tac >>
  qpat_assum `EL i paths = cut0` mp_tac >>
  qpat_assum `EL i levels = _` mp_tac >>
  qpat_assum `EL i gcs = _` mp_tac >>
  qpat_assum `i < LENGTH gcs` mp_tac >>
  qpat_assum `i < LENGTH cuts` mp_tac >>
  qpat_assum `Abbrev (P = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[DROP_CONS_EL,FLAT,APPEND_ASSOC]
QED

Resume request_cut_packet_selected_keys[body_fact]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.SPECL
    [`N`,`C7`,`C8`,`root_sf`,`root_tf`,`root_entry`,`packet`,`acts`,`blocks`,`calls`,
     `ms_tab`,`es_tab`,`ks_tab`,`rooted_eval`,`p`,`d`,`q8`,`raw_slots`,`sites`,`unused`,
     `cut0`,`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,
     `cut1`,`cut2`,`later`,`bbi`,`bti`,`psi`,`xsi`,`ysi`,`rhoi`,`ini`,`hi`,
     `be`,`hbe`,`counti`,`fronti`,`closedi`,`resti`,`ms`,`ks`,`fuel`,`cut3`,
     `cut4`,`prev`,`row_run`,`gps`,`gas`,`rest`,`prev_keys`,`active_keys`]
    request_cut_packet_level_body) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[Abbr `prev`,Abbr `row_run`,Abbr `prev_keys`,Abbr `active_keys`]) >>
  simp[GSYM markerTheory.Abbrev_def,Abbr `partial`,Abbr `rest`]
QED

Resume request_cut_packet_selected_keys[last_visit]:
  `!t. P (SUC i) t /\
    ((~(?u. FST (run_at (SUC i) t) = OK u) /\
      ~(?ir u. FST (run_at (SUC i) t) = IntRet ir u)) ==>
      FST (run_at i s) = FST (run_at (SUC i) t) /\
      SND (run_at i s) = EL i keyss ++ SND (run_at (SUC i) t))` by
    simp[Abbr `P`,Abbr `run_at`] >>
  qpat_assum `SUC i = LENGTH cuts` (fn eq =>
    simp_tac bool_ss [eq] >>
    qpat_x_assum `if SUC i = LENGTH cuts then _ else _`
      (mp_tac o REWRITE_RULE [eq,COND_CLAUSES])) >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- suspend "last_body" >>
  suspend "last_fresh"
QED

Resume request_cut_packet_selected_keys[last_body]:
  `?be hbe. bei = SOME (be,hbe)` by
    (qpat_assum `IS_SOME bei` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     Cases_on `bei` >> simp[] >> PairCases_on `x` >> metis_tac[]) >>
  qpat_assum `!be hbe. bei = SOME (be,hbe) /\ _ ==> _`
    (qspecl_then [`be`,`hbe`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `SUC i = LENGTH cuts` (fn eq =>
    qpat_assum `!t. P (SUC i) t /\ _` (fn th =>
      Cases_on `partial` >> simp[NoAsms,REWRITE_RULE [eq] th]))
QED

Resume request_cut_packet_selected_keys[last_fresh]:
  `gas = [] /\ active_keys = []` by
    (qpat_assum `LIST_REL (LIST_REL _) (TAKE cut3 ms) gas` mp_tac >>
     qpat_assum `cut3 = 0` (fn th => simp[NoAsms,th,Abbr `active_keys`]) >>
     simp[listTheory.LIST_REL_LENGTH]) >>
  mp_tac (Q.SPECL
    [`N`,`C7`,`C8`,`root_sf`,`root_tf`,`root_entry`,`packet`,`acts`,`blocks`,`calls`,
     `ms_tab`,`es_tab`,`ks_tab`,`rooted_eval`,`p`,`d`,`q8`,`raw_slots`,`sites`,`unused`,
     `cut0`,`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,
     `cut1`,`cut2`,`later`,`bbi`,`bti`,`psi`,`xsi`,`ysi`,`rhoi`,`ini`,`hi`,
     `counti`,`fronti`,`closedi`,`resti`,`fuel`,`cut4`,`prev`,`row_run`,`gps`,
     `rest`,`prev_keys`] request_cut_packet_level_fresh) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[Abbr `prev`,Abbr `row_run`,Abbr `prev_keys`]) >>
  `FOLDL (\r row. case r of OK st => row_run row st | other => other)
     (OK (enti with vs_gas_readings := FLAT gps ++ rest)) (prev ++ [(bbi,cut2,cut4)]) =
    partial` by
    (qpat_assum `s = enti with vs_gas_readings := _` mp_tac >>
     qpat_assum `gas = []` mp_tac >>
     simp[NoAsms,Abbr `partial`,Abbr `rest`]) >>
  qpat_assum `FOLDL _ (OK (enti with vs_gas_readings := FLAT gps ++ rest)) _ = partial`
    (fn th => simp_tac bool_ss [th]) >>
  `EL i keyss = prev_keys` by
    (qpat_assum `EL i keyss = prev_keys ++ active_keys` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `active_keys = []` (fn th => simp[NoAsms,th])) >>
  Cases_on `partial` >> simp[NoAsms]
  >- (qpat_assum `SUC i = LENGTH cuts` (fn eq =>
        qpat_assum `!t. P (SUC i) t /\ _` (fn th =>
          simp[NoAsms,REWRITE_RULE [eq] th]))) >>
  map_every (fn pat => qpat_assum pat (fn th => simp_tac bool_ss [th]))
    [`EL i keyss = prev_keys`, `FST (run_at i s) = _`, `SND (run_at i s) = _`,
     `s = enti with vs_gas_readings := _`, `gas = []`] >>
  simp[NoAsms]
QED

Resume request_cut_packet_selected_keys[caller_visit]:
  `SUC i < LENGTH cuts` by decide_tac >>
  qpat_assum `SUC i <> LENGTH cuts` (fn neq =>
    simp_tac bool_ss [neq] >>
    qpat_x_assum `if SUC i = LENGTH cuts then _ else _`
      (mp_tac o REWRITE_RULE [neq,COND_CLAUSES])) >>
  disch_then strip_assume_tac >>
  drule_all request_cut_packet_level_call_records >>
  strip_tac >>
  qpat_assum `!be hbe. bei = SOME (be,hbe) /\ _ ==> _`
    (qspecl_then [`be`,`hbe`] mp_tac) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  Cases_on `partial` >> simp[NoAsms] >>
  disch_then strip_assume_tac
  >- suspend "open_call" >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume request_cut_packet_selected_keys[open_call]:
  rename1 `v.vs_inst_idx = cut3 + LENGTH psi` >>
  `v.vs_inst_idx = LENGTH psi + cut3` by
    (qpat_assum `v.vs_inst_idx = cut3 + LENGTH psi` (fn th =>
       simp[NoAsms,th,arithmeticTheory.ADD_COMM])) >>
  `FLOOKUP blocks (cut0,cut2) =
    SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,SOME (be,hbe),counti,fronti,closedi,resti)` by
    (qpat_assum `FLOOKUP blocks (cut0,cut2) = SOME _` mp_tac >>
     qpat_assum `bei = SOME (be,hbe)` (fn th => simp[NoAsms,th])) >>
  drule_all request_cut_packet_level_call >>
  disch_then (qspec_then `sfi` strip_assume_tac) >>
  qabbrev_tac `child = child_entry with vs_gas_readings := rest` >>
  `FST (EL (SUC i) levels) = csf /\ EL (SUC i) depths = cut2` by
    suspend "child_level" >>
  `P (SUC i) child` by
    (simp_tac bool_ss [Abbr `P`,Abbr `child`,Abbr `rest`] >>
     strip_tac >>
     qexistsl_tac [`ctf`,`cut2`,`child_entry`,`corder`,`cres`,`crest`] >>
     map_every (fn pat => qpat_assum pat (fn th => simp_tac bool_ss [th]))
       [`EL (SUC i) paths = _`,`FST (EL (SUC i) levels) = csf`,
        `FLOOKUP acts ((cut2,cid)::cut0) = SOME _`]) >>
  `run_at (SUC i) child =
     (run_blocks (fuel-cut2) C7 csf child,
      MAP FST (trace_gas (trace_blocks ((cut2,cid)::cut0) cut2 (fuel-cut2) C7 csf child)))` by
    (`SUC i < LENGTH levels` by decide_tac >>
     simp_tac bool_ss [Abbr `run_at`] >>
     map_every (fn pat => qpat_assum pat (fn th => simp_tac bool_ss [th]))
       [`SUC i < LENGTH levels`,`EL (SUC i) paths = _`,
        `EL (SUC i) depths = cut2`,`FST (EL (SUC i) levels) = csf`]) >>
  map_every (fn pat => qpat_assum pat (fn th =>
    simp_tac (srw_ss()) [NoAsms,th]))
    [`decode_invoke (EL cut3 xsi) = SOME _`, `lookup_function _ C7.ctx_functions = SOME csf`,
     `eval_operands _ v = SOME _`,`setup_callee csf _ v = SOME _`] >>
  simp_tac (srw_ss()) [NoAsms] >>
  qpat_assum `Abbrev (child = _)` (fn th =>
    simp_tac bool_ss [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  qpat_assum `!r. run_blocks (fuel-cut2) C7 csf _ = r /\ _ ==> _`
    (qspec_then `FST (run_at (SUC i) child)` mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  qpat_assum `(∀w. exec_block (fuel-cut2) C7 bbi v <> OK w) ==> _` mp_tac >>
  qpat_assum `exec_block (fuel-cut2) C7 bbi v = _` (fn th =>
    simp_tac bool_ss [th]) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `MAP FST (trace_gas (trace_block cut0 cut2 _ C7 sfi bbi v)) = _`
    (fn th => simp_tac bool_ss [th]) >>
  qpat_assum `run_at (SUC i) child = _` (fn th => simp[NoAsms,th])
QED

Resume request_cut_packet_selected_keys[child_level]:
  qabbrev_tac `cc = EL (SUC i) cuts` >> PairCases_on `cc` >>
  `EL (SUC i) cuts = (cc0,cc1,cc2,cc3,cc4)` by metis_tac[Abbr `cc`] >>
  qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts /\ _ ==> _`
    (qspecl_then [`SUC i`,`cc0`,`cc1`,`cc2`,`cc3`,`cc4`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  `cc0 = (cut2,cid)::cut0` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`EL (SUC i) paths = _`,`paths = MAP _ cuts`,`EL (SUC i) cuts = _`,
       `SUC i < LENGTH cuts`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[EL_MAP]) >>
  conj_tac >-
    (qpat_assum `EL (SUC i) levels = _` (fn th => rewrite_tac[th,pairTheory.FST]) >>
     qpat_assum `FLOOKUP acts cc0 = SOME _` mp_tac >>
     qpat_assum `FLOOKUP acts ((cut2,cid)::cut0) = SOME _` mp_tac >>
     qpat_assum `cc0 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  `SUC i < LENGTH paths` by decide_tac >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`EL (SUC i) paths = _`,`SUC i < LENGTH paths`,`Abbrev (depths = _)`] >>
  POP_ASSUM_LIST (K all_tac) >> simp[markerTheory.Abbrev_def,EL_MAP]
QED

Finalise request_cut_packet_selected_keys
