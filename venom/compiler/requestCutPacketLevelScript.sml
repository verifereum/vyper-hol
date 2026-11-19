Theory requestCutPacketLevel
Ancestors
  requestCutPacketPlan requestCutPacketActive requestCutPacketExecution
  dftPacketFillingBoundary dftFinitePacket dftGasFromListTraceDefs dftIndexedExec
  venomExecSemantics venomState list rich_list arithmetic finite_map

(* Split one activation into completed predecessor blocks and its cut row.
   A stopped activation has already emitted its entire native key prefix. *)
Theorem request_cut_packet_level_body:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a sf tf inc entry order res nrest
    ds e later bb bt ps xs ys row_order hin h0 be hbe row_count front closed brest
    ms ks fuel k z prev row_run gss kgss tail prev_keys active_keys.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    order = ds ++ e::later /\ e = inc + SUC (LENGTH ds) /\ e <= fuel /\ N <= fuel /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,row_order,hin,h0,SOME (be,hbe),row_count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
    k <= LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE row_count row_order)) /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (MAP (\f. FLAT (THE (FLOOKUP ms_tab (a,f)))) ds) gss /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE k xs /\
    prev = MAP (\f. (FST (THE (FLOOKUP blocks (a,f))),f,
      DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
        (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds /\
    row_run = (\(b,f,is) s. case eval_phis s b.bb_instructions of
      OK sp => FOLDR (dft_exec_cons (fuel-f) C7) OK is
                    (sp with vs_inst_idx := phi_prefix_length b.bb_instructions)
    | other => other) /\
    prev_keys = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) ds) /\
    active_keys = FLAT (TAKE k ks) ==>
    case FOLDL (\r row. case r of OK s => row_run row s | other => other)
      (OK (entry with vs_gas_readings := FLAT gss ++ FLAT kgss ++ tail))
      (prev ++ [(bb,e,z)]) of
      OK u => u.vs_inst_idx = LENGTH ps + k /\ u.vs_gas_readings = tail /\
        FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u /\
        (!r. exec_block (fuel-e) C7 bb u = r /\ ~(?v. r = OK v) ==>
          run_blocks (fuel-inc) C7 sf
            (entry with vs_gas_readings := FLAT gss ++ FLAT kgss ++ tail) = r /\
          MAP FST (trace_gas (trace_blocks a inc (fuel-inc) C7 sf
            (entry with vs_gas_readings := FLAT gss ++ FLAT kgss ++ tail))) =
            prev_keys ++ active_keys ++ MAP FST (trace_gas (trace_block a e
              (fuel-e) C7 sf bb u)))
    | stopped => ~(?ir u. stopped = IntRet ir u) /\
        run_blocks (fuel-inc) C7 sf
          (entry with vs_gas_readings := FLAT gss ++ FLAT kgss ++ tail) = stopped /\
        ?extra. prev_keys ++ active_keys =
          MAP FST (trace_gas (trace_blocks a inc (fuel-inc) C7 sf
            (entry with vs_gas_readings := FLAT gss ++ FLAT kgss ++ tail))) ++ extra
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `fill = entry with vs_gas_readings := FLAT gss ++ FLAT kgss ++ tail` >>
  qabbrev_tac `v = hin with vs_gas_readings := FLAT kgss ++ tail` >>
  qabbrev_tac `fold = (\r row. case r of OK s => row_run row s | other => other)` >>
  qabbrev_tac `vprev = FOLDL fold (OK fill) prev` >>
  `case vprev of
      OK u => u = v /\
        run_blocks (fuel-inc) C7 sf fill = run_blocks (SUC (fuel-e)) C7 sf v /\
        MAP FST (trace_gas (trace_blocks a inc (fuel-inc) C7 sf fill)) =
          prev_keys ++ MAP FST (trace_gas (trace_blocks a (e-1) (SUC (fuel-e)) C7 sf v))
    | stopped => ~(?ir u. stopped = IntRet ir u) /\
        run_blocks (fuel-inc) C7 sf fill = stopped /\
        ?extra. prev_keys =
          MAP FST (trace_gas (trace_blocks a inc (fuel-inc) C7 sf fill)) ++ extra` by
    suspend "predecessors" >>
  `?sp. eval_phis v bb.bb_instructions = OK sp /\
    lookup_block v.vs_current_bb sf.fn_blocks = SOME bb /\
    FOLDR (dft_exec_cons (fuel-e) C7) OK z
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) /\
    (case FOLDR (dft_exec_cons (fuel-e) C7) OK z
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) of
       OK u => u.vs_inst_idx = LENGTH ps + k /\ u.vs_gas_readings = tail /\
         exec_block (fuel-e) C7 bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
           exec_block (fuel-e) C7 bb u /\
         MAP FST (trace_gas (trace_block a e (fuel-e) C7 sf bb
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))) =
             active_keys ++ MAP FST (trace_gas (trace_block a e (fuel-e) C7 sf bb u))
     | stopped => ~(?ir u. stopped = IntRet ir u) /\
         run_blocks (SUC (fuel-e)) C7 sf v = stopped /\
         ?extra. active_keys =
           MAP FST (trace_gas (trace_blocks a (e-1) (SUC (fuel-e)) C7 sf v)) ++ extra)` by
    (qpat_assum `active_keys = _` SUBST1_TAC >>
     mp_tac (Q.SPECL
       [`N`,`C7`,`C8`,`root_sf`,`root_tf`,`root_entry`,`packet`,`acts`,`blocks`,`calls`,
        `ms_tab`,`es_tab`,`ks_tab`,`rooted_eval`,`p`,`d`,`q8`,`raw_slots`,`sites`,`unused`,
        `a`,`e`,`sf`,`tf`,`inc`,`entry`,`order`,`res`,`nrest`,`ds`,`later`,
        `bb`,`bt`,`ps`,`xs`,`ys`,`row_order`,`hin`,`h0`,`be`,`hbe`,`row_count`,`front`,
        `closed`,`brest`,`ms`,`ks`,`fuel`,`k`,`kgss`,`tail`,`z`,`v`]
       request_cut_packet_active_body) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[Abbr `v`]) >>
     DISCH_THEN ACCEPT_TAC) >>
  `fold vprev (bb,e,z) = FOLDL fold (OK fill) (prev ++ [(bb,e,z)])` by
    simp[Abbr `vprev`,FOLDL_APPEND] >>
  qpat_assum `fold vprev _ = _` (SUBST1_TAC o SYM) >>
  Cases_on `vprev` >> simp[Abbr `fold`,NoAsms]
  >- suspend "active" >>
  qpat_x_assum `case _ of OK u => u = v /\ _
    | Halt _ => _ | Abort _ _ => _ | IntRet _ _ => _ | Error _ => _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [NoAsms]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac `extra ++ active_keys` >> simp[APPEND_ASSOC]
QED

Resume request_cut_packet_level_body[predecessors]:
  mp_tac (Q.SPECL
    [`N`,`C7`,`C8`,`root_sf`,`root_tf`,`root_entry`,`packet`,`acts`,`blocks`,`calls`,
     `ms_tab`,`es_tab`,`ks_tab`,`rooted_eval`,`p`,`d`,`q8`,`raw_slots`,`sites`,`unused`,
     `a`,`sf`,`tf`,`inc`,`entry`,`order`,`res`,`nrest`,`ds`,`e`,`later`,`fuel`,`gss`,
     `FLAT kgss ++ tail`,`MAP (\(f:num). FLAT (THE (FLOOKUP ms_tab (a:(num # num) list,f)))) ds`,
     `MAP (\(f:num). FLAT (THE (FLOOKUP ks_tab (a:(num # num) list,f)))) ds`,`prev`,`row_run`]
    request_cut_packet_predecessor_plan) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  `fuel-inc-LENGTH ds = SUC (fuel-e) /\ e-1 = inc + LENGTH ds` by decide_tac >>
  `(case THE (FLOOKUP blocks (a,e)) of
      (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) => inf) = hin` by simp[] >>
  simp[Abbr `vprev`,Abbr `fold`,Abbr `fill`,Abbr `v`] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Resume request_cut_packet_level_body[active]:
  qpat_x_assum `case OK _ of OK u => u = v /\ _
    | Halt _ => _ | Abort _ _ => _ | IntRet _ _ => _ | Error _ => _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [exec_result_case_def]) >>
  `row_run (bb,e,z) v = FOLDR (dft_exec_cons (fuel-e) C7) OK z
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (qpat_assum `row_run = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `eval_phis v bb.bb_instructions = OK sp` (fn th => simp[NoAsms,th])) >>
  qpat_assum `row_run (bb,e,z) v = _` (fn th =>
    qpat_assum `_ = v` (fn eq => simp_tac bool_ss [eq,th])) >>
  Cases_on `FOLDR (dft_exec_cons (fuel-e) C7) OK z
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[NoAsms]
  >- suspend "enter_call" >>
  qpat_x_assum `case _ of OK u => u.vs_inst_idx = _ /\ _
    | Halt _ => _ | Abort _ _ => _ | IntRet _ _ => _ | Error _ => _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [NoAsms]) >>
  gvs[APPEND_ASSOC] >> qexists_tac `extra` >> simp[]
QED

Resume request_cut_packet_level_body[enter_call]:
  rename1 `u.vs_inst_idx = k + LENGTH ps /\ _` >>
  qpat_x_assum `case OK u of OK t => t.vs_inst_idx = _ /\ _
    | Halt _ => _ | Abort _ _ => _ | IntRet _ _ => _ | Error _ => _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [exec_result_case_def]) >>
  conj_tac >- simp[arithmeticTheory.ADD_COMM] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `OK u = FOLDR _ OK (TAKE k xs) _` (ACCEPT_TAC o SYM) ORELSE
     qpat_assum `FOLDR _ OK (TAKE k xs) _ = OK u` ACCEPT_TAC) >>
  strip_tac >>
  `~(?v. exec_block (fuel-e) C7 bb u = OK v)` by (simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  `SUC (e-1) = e` by decide_tac >>
  drule_all request_cut_native_block_stopped >>
  disch_then (qspecl_then [`e-1`,`a`] strip_assume_tac) >>
  gvs[APPEND_ASSOC]
QED

Finalise request_cut_packet_level_body

Theorem request_cut_packet_level_fresh:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a sf tf inc entry order res nrest
    ds e later bb bt ps xs ys row_order hin h0 row_count front closed brest
    fuel z prev row_run gss tail prev_keys.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    order = ds ++ e::later /\ e = inc + SUC (LENGTH ds) /\ e <= fuel /\ N <= fuel /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,row_order,hin,h0,NONE,row_count,front,closed,brest) /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (MAP (\f. FLAT (THE (FLOOKUP ms_tab (a,f)))) ds) gss /\
    prev = MAP (\f. (FST (THE (FLOOKUP blocks (a,f))),f,
      DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
        (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds /\
    row_run = (\(b,f,is) s. case eval_phis s b.bb_instructions of
      OK sp => FOLDR (dft_exec_cons (fuel-f) C7) OK is
                    (sp with vs_inst_idx := phi_prefix_length b.bb_instructions)
    | other => other) /\
    prev_keys = FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (a,f)))) ds) /\
    (!gs. ?sp u. eval_phis (hin with vs_gas_readings := gs) bb.bb_instructions = OK sp /\
       FOLDR (dft_exec_cons (fuel-e) C7) OK z
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK u) ==>
    case FOLDL (\r row. case r of OK s => row_run row s | other => other)
      (OK (entry with vs_gas_readings := FLAT gss ++ tail)) (prev ++ [(bb,e,z)]) of
      OK u => T
    | stopped => ~(?ir u. stopped = IntRet ir u) /\
        run_blocks (fuel-inc) C7 sf (entry with vs_gas_readings := FLAT gss ++ tail) = stopped /\
        ?extra. prev_keys = MAP FST (trace_gas (trace_blocks a inc (fuel-inc) C7 sf
          (entry with vs_gas_readings := FLAT gss ++ tail))) ++ extra
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `fill = entry with vs_gas_readings := FLAT gss ++ tail` >>
  qabbrev_tac `fold = (\r row. case r of OK s => row_run row s | other => other)` >>
  mp_tac (Q.SPECL
    [`N`,`C7`,`C8`,`root_sf`,`root_tf`,`root_entry`,`packet`,`acts`,`blocks`,`calls`,
     `ms_tab`,`es_tab`,`ks_tab`,`rooted_eval`,`p`,`d`,`q8`,`raw_slots`,`sites`,`unused`,
     `a`,`sf`,`tf`,`inc`,`entry`,`order`,`res`,`nrest`,`ds`,`e`,`later`,`fuel`,`gss`,`tail`,
     `MAP (\(f:num). FLAT (THE (FLOOKUP ms_tab (a:(num # num) list,f)))) ds`,
     `MAP (\(f:num). FLAT (THE (FLOOKUP ks_tab (a:(num # num) list,f)))) ds`,`prev`,`row_run`]
    request_cut_packet_predecessor_plan) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  simp[GSYM markerTheory.Abbrev_def, FOLDL_APPEND] >>
  Cases_on `FOLDL fold (OK fill) prev` >> simp[Abbr `fold`] >>
  qpat_assum `!gs. ?sp u. eval_phis _ _ = _ /\ _` (qspec_then `tail` strip_assume_tac) >>
  gvs[]
QED
