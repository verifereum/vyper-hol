Theory requestCutPacketClosedRow
Ancestors
  requestCutNativeBoundary dftFinitePacket dftPacketEntryReplay dftContractGas
  dftPacketFillingBoundary dftPacketClosedRowNative dftGasFromListTraceDefs
  dftGasFromListReadings dftGasToListReplay venomExecProofs venomExecSemantics
  venomInst venomState venomWf o1PassContract dftIndexedExec dftRunRel
  passSimulationDefs stateEquiv list rich_list finite_map sorting arithmetic

Theorem request_cut_packet_closed_row_keys:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count post rest ms ks fuel gs tail.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,OK post,T,SOME rest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
    N <= fuel /\ 0 < e /\ ~post.vs_halted /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
    ?sp. eval_phis (hin with vs_gas_readings := gs ++ tail) bb.bb_instructions = OK sp /\
      FOLDR (dft_exec_cons (fuel-e) C7) OK
        (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
        exec_block (fuel-e) C7 bb
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
      (case exec_block (fuel-e) C7 bb
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) of
        OK u => u = post with vs_gas_readings := tail /\
          run_blocks (SUC (fuel-e)) C7 sf (hin with vs_gas_readings := gs ++ tail) =
            run_blocks (fuel-e) C7 sf u /\
          MAP FST (trace_gas (trace_blocks a (e-1) (SUC (fuel-e)) C7 sf
            (hin with vs_gas_readings := gs ++ tail))) = FLAT ks ++
              MAP FST (trace_gas (trace_blocks a e (fuel-e) C7 sf u))
      | stopped => ~(?ir u. stopped = IntRet ir u) /\
          run_blocks (SUC (fuel-e)) C7 sf
          (hin with vs_gas_readings := gs ++ tail) = stopped /\
          ?extra. FLAT ks = MAP FST (trace_gas
            (trace_blocks a (e-1) (SUC (fuel-e)) C7 sf
              (hin with vs_gas_readings := gs ++ tail))) ++ extra)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP blocks (a,e) = SOME
    (bb,bt,ps,xs,ys,order_row,hin,h0,SOME (be,hbe),num_done,OK post,T,SOME rest)` >>
  `?oldsp. bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    bb_well_formed bb /\ lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
    eval_phis hin (ps ++ ys) = OK oldsp /\
    FOLDR (dft_exec_cons (N-e) C8) OK (DROP (phi_prefix_length (ps ++ ys)) ps)
      (oldsp with vs_inst_idx := phi_prefix_length (ps ++ ys)) = OK be /\
    be.vs_inst_idx = LENGTH ps /\ num_done = LENGTH ys /\ LENGTH ys = LENGTH xs /\
    PERM order_row (COUNT_LIST (LENGTH xs)) /\ xs <> [] /\
    LENGTH ms = LENGTH xs /\ LENGTH ks = LENGTH xs` by
    suspend "row_data" >>
  `?sp. eval_phis (hin with vs_gas_readings := gs ++ tail) bb.bb_instructions = OK sp /\
    FOLDR (dft_exec_cons (fuel-e) C7) OK
      (DROP (phi_prefix_length bb.bb_instructions) ps)
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
        OK (be with vs_gas_readings := gs ++ tail)` by
    (asm_rewrite_tac[] >> irule dft_packet_body_entry_replay >> simp[] >>
     qexistsl [`C8`,`N-e`,`oldsp`,`ys`] >> simp[]) >>
  qexists_tac `sp` >> asm_rewrite_tac[] >>
  `phi_prefix_length bb.bb_instructions <= LENGTH ps` by
    (`EVERY (\i. i.inst_opcode <> PHI) xs` by
       (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
     simp[dft_phi_prefix_append,phi_prefix_length_le]) >>
  mp_tac (Q.SPECL [`bb`,`ps`,`xs`,
     `sp with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
     `be with vs_gas_readings := gs ++ tail`]
    (Q.INST [`f` |-> `fuel-e`, `C` |-> `C7`, `p` |-> `a`, `d` |-> `e`]
      request_cut_native_body_projection)) >>
  impl_tac >- gvs[] >> strip_tac >>
  `is_terminator (LAST xs).inst_opcode` by
    (qpat_assum `bb_well_formed bb` mp_tac >>
     qpat_assum `bb.bb_instructions = ps ++ xs` mp_tac >>
     qpat_assum `xs <> []` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[bb_well_formed_def,LAST_APPEND_NOT_NIL]) >>
  `exec_block (fuel-e) C7 bb (be with vs_gas_readings := gs ++ tail) =
   FOLDR (dft_exec_cons (fuel-e) C7) OK xs (be with vs_gas_readings := gs ++ tail)` by
    (irule native_exec_block_terminated_fold >> simp[DROP_APPEND]) >>
  conj_tac
  >- (`bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode` by
         simp[LAST_APPEND_NOT_NIL] >>
      `(LAST bb.bb_instructions).inst_opcode <> PHI` by
        (qpat_assum `is_terminator (LAST bb.bb_instructions).inst_opcode` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> Cases_on `(LAST bb.bb_instructions).inst_opcode` >> simp[is_terminator_def]) >>
      `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
        metis_tac[phi_prefix_length_lt_last_non_phi] >>
      CONV_TAC SYM_CONV >> irule native_exec_block_terminated_fold >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions`,
         `is_terminator (LAST bb.bb_instructions).inst_opcode`,
         `bb.bb_instructions = ps ++ xs`] >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[DROP_EQ_NIL,last_drop]) >>
  `?kgss. gs = FLAT kgss /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) ms kgss` by
    (irule dft_packet_flat_filling_split >> simp[]) >>
  `?extra. FLAT ks = MAP FST (trace_gas
    (trace_block a e (fuel-e) C7 sf bb (be with vs_gas_readings := gs ++ tail))) ++ extra` by
    suspend "row_keys" >>
  `SUC (e-1) = e` by decide_tac >>
  `exec_block (fuel-e) C7 bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
    FOLDR (dft_exec_cons (fuel-e) C7) OK xs (be with vs_gas_readings := gs ++ tail)` by
    metis_tac[] >>
  qabbrev_tac `r = FOLDR (dft_exec_cons (fuel-e) C7) OK xs (be with vs_gas_readings := gs ++ tail)` >>
  `exec_block (fuel-e) C7 bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = r` by
    simp[Abbr `r`] >>
  `terminates r ==> residual_result tail (OK post) r` by
    suspend "residual" >>
  `!ir u. r <> IntRet ir u` by
    (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     qpat_assum `terminates (IntRet _ _) ==> _` mp_tac >>
     simp[NoAsms,terminates_def,residual_result_def,lift_result_def]) >>
  `run_blocks (SUC (fuel-e)) C7 sf (hin with vs_gas_readings := gs ++ tail) =
    (case r of OK u => if u.vs_halted then Halt u else run_blocks (fuel-e) C7 sf u
       | other => other)` by suspend "native_run" >>
  `MAP FST (trace_gas (trace_blocks a (e-1) (SUC (fuel-e)) C7 sf
      (hin with vs_gas_readings := gs ++ tail))) =
    MAP FST (trace_gas (trace_block a e (fuel-e) C7 sf bb
      (be with vs_gas_readings := gs ++ tail))) ++
    (case r of OK u => if u.vs_halted then [] else
       MAP FST (trace_gas (trace_blocks a e (fuel-e) C7 sf u))
     | _ => [])` by suspend "native_trace" >>
  `exec_block (fuel-e) C7 bb (sp with vs_inst_idx := phi_prefix_length (ps ++ xs)) = r` by
    (qpat_assum `bb.bb_instructions = ps ++ xs` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  map_every (fn pat => qpat_assum pat (fn th => rewrite_tac[th]))
    [`exec_block (fuel-e) C7 bb (sp with vs_inst_idx := phi_prefix_length (ps ++ xs)) = r`,
     `exec_block (fuel-e) C7 bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = r`,
     `run_blocks (SUC (fuel-e)) C7 sf (hin with vs_gas_readings := gs ++ tail) = _`,
     `MAP FST (trace_gas (trace_blocks a (e-1) (SUC (fuel-e)) C7 sf _)) = _`] >>
  Cases_on `r` >> simp[NoAsms]
  >- suspend "row_success" >>
  TRY (qexists_tac `extra` >> first_assum ACCEPT_TAC) >>
  rename1 `Abbrev (IntRet ir u = _)` >>
  qpat_assum `!x y. IntRet ir u <> IntRet x y`
    (qspecl_then [`ir`,`u`] mp_tac) >> simp[NoAsms]
QED

Resume request_cut_packet_closed_row_keys[row_data]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (fn row => qpat_assum `FLOOKUP blocks (a,e) = SOME _`
      (strip_assume_tac o MATCH_MP row)) >>
  qpat_x_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
    (fn lookup =>
      qpat_x_assum `FLOOKUP acts a = SOME _`
        (mp_tac o REWRITE_RULE [lookup, optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
      disch_then (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS) >> assume_tac lookup) >>
  qpat_x_assum `case SOME (be,hbe) of NONE => _ | SOME v => _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `MEM sf C7.ctx_functions` by
    (qpat_assum `!a sf tf inc entry order res nrest.
       FLOOKUP acts a = _ ==> MEM sf C7.ctx_functions /\ _`
       (fn clause => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
         (ACCEPT_TAC o CONJUNCT1 o MATCH_MP clause))) >>
  `wf_function sf` by
    (qpat_assum `o1_ctx_shape C7` (mp_tac o MATCH_MP o1_ctx_shape_wf_functions) >>
     qpat_assum `MEM sf C7.ctx_functions` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[EVERY_MEM]) >>
  `MEM bb sf.fn_blocks` by
    (qpat_assum `lookup_block bb.bb_label sf.fn_blocks = SOME bb` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[venomExecPropsTheory.FIND_MEM,lookup_block_def]) >>
  `bb_well_formed bb` by
    (qpat_assum `wf_function sf` mp_tac >>
     qpat_assum `MEM bb sf.fn_blocks` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[wf_function_def]) >>
  `xs <> []` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`bb_well_formed bb`,`bb.bb_instructions = ps ++ xs`,
        `EVERY (\i. is_pseudo i.inst_opcode) ps`] >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `xs` >> simp[] >>
     rpt strip_tac >> gvs[bb_well_formed_def,EVERY_MEM] >>
     `MEM (LAST bb.bb_instructions) bb.bb_instructions` by simp[LAST_MEM] >>
     `is_pseudo (LAST bb.bb_instructions).inst_opcode` by metis_tac[] >>
     Cases_on `(LAST bb.bb_instructions).inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
    (qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]) >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
    (drule_all_then (fn th => map_every assume_tac [cj 1 th,cj 3 th])) >>
  qexists_tac `sp` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  map_every (fn pat => TRY (qpat_assum pat mp_tac))
    [`bt.bb_instructions = ps ++ ys`, `eval_phis hin bt.bb_instructions = OK sp`,
     `FOLDR _ _ _ _ = OK be`, `LENGTH xs = LENGTH ys`,
     `LENGTH ks = LENGTH ms`, `LENGTH ms = LENGTH xs`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]
QED

Resume request_cut_packet_closed_row_keys[row_keys]:
  `!q. q < LENGTH xs ==> MEM q (TAKE num_done order_row)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`PERM order_row (COUNT_LIST (LENGTH xs))`,`num_done = LENGTH ys`,`LENGTH ys = LENGTH xs`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule PERM_LENGTH >> drule PERM_MEM_EQ >>
     simp[MEM_COUNT_LIST, LENGTH_COUNT_LIST] >>
     rpt strip_tac >> gvs[TAKE_LENGTH_TOO_LONG]) >>
  `trace_block a e (fuel-e) C7 sf bb (be with vs_gas_readings := gs ++ tail) =
   trace_block a e (fuel-e) C7 sf
    <|bb_label := be.vs_current_bb; bb_instructions :=
      REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
    (be with vs_gas_readings := gs ++ tail)` by
    (irule native_trace_block_suffix_cong >> simp[DROP_APPEND]) >>
  simp[] >>
  `?extra. FLAT (TAKE (LENGTH xs) ks) = MAP FST (trace_gas
    (trace_block a e (fuel-e) C7 sf
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE (LENGTH xs) xs|>
      (be with vs_gas_readings := FLAT kgss ++ tail))) ++ extra` by
    (irule dft_packet_row_cut_keys >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `FLOOKUP acts a = _` (irule_at Any) >>
     qpat_assum `FLOOKUP blocks (a,e) = _` (irule_at Any) >>
     qpat_assum `FLOOKUP ms_tab (a,e) = _` (irule_at Any) >>
     qpat_assum `FLOOKUP ks_tab (a,e) = _` (irule_at Any) >>
     simp[TAKE_LENGTH_TOO_LONG]) >>
  qexists_tac `extra` >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLAT (TAKE _ ks) = _`, `LENGTH ks = LENGTH xs`, `gs = FLAT kgss`,
      `be.vs_inst_idx = LENGTH ps`,
      `trace_block a e (fuel-e) C7 sf bb _ = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[TAKE_LENGTH_TOO_LONG]
QED

Resume request_cut_packet_closed_row_keys[native_run]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb`,
     `eval_phis (hin with vs_gas_readings := gs ++ tail) bb.bb_instructions = OK sp`,
     `exec_block (fuel-e) C7 bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = r`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [run_blocks_def])) >> simp[]
QED

Resume request_cut_packet_closed_row_keys[native_trace]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb`,
     `eval_phis (hin with vs_gas_readings := gs ++ tail) bb.bb_instructions = OK sp`,
     `exec_block (fuel-e) C7 bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = r`,
     `trace_gas (trace_block a e (fuel-e) C7 sf bb
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) = _`,
     `SUC (e-1) = e`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [cj 3 trace_defs])) >>
  Cases_on `r` >> simp[trace_gas_append, MAP_APPEND] >>
  rename1 `MAP FST (trace_gas (if u.vs_halted then _ else _)) = _` >>
  Cases_on `u.vs_halted` >> simp[]
QED

Resume request_cut_packet_closed_row_keys[row_success]:
  rename1 `Abbrev (OK u = _)` >>
  `FOLDR (dft_exec_cons (fuel-e) C7) OK xs
    (be with vs_gas_readings := gs ++ tail) = OK u` by
    (qpat_assum `Abbrev (OK u = _)`
      (ACCEPT_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def])) >>
  `u = post with vs_gas_readings := tail` by
    (qpat_assum `terminates (OK u) ==> _`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [terminates_def])) >>
  `MAP FST (trace_gas (trace_block a e (fuel-e) C7 sf bb
      (be with vs_gas_readings := gs ++ tail))) = FLAT ks` by
    suspend "key_success" >>
  gvs[]
QED

Resume request_cut_packet_closed_row_keys[residual]:
  qpat_assum `Abbrev (r = _)`
    (fn th => rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
  strip_tac >>
  mp_tac (Q.SPECL
    [`N`,`C7`,`C8`,`root_sf`,`root_tf`,`root_entry`,`packet`,`acts`,`blocks`,`calls`,
     `ms_tab`,`es_tab`,`ks_tab`,`rooted_eval`,`p`,`d`,`q8`,`raw_slots`,`sites`,`unused`,
     `a`,`e`,`sf`,`tf`,`inc`,`entry`,`order`,`res`,`nrest`,
     `bb`,`bt`,`ps`,`xs`,`ys`,`order_row`,`hin`,`h0`,`be`,`hbe`,
     `num_done`,`OK post`,`rest`,`ms`,`fuel`,`gs`,`tail`]
    dft_packet_closed_row_residual) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- simp[NoAsms] >>
      qexists_tac `fuel-e` >> first_assum ACCEPT_TAC) >>
  DISCH_THEN ACCEPT_TAC
QED

Resume request_cut_packet_closed_row_keys[key_success]:
  mp_tac (Q.SPECL
    [`N`,`C7`,`C8`,`root_sf`,`root_tf`,`root_entry`,`packet`,`acts`,`blocks`,`calls`,
     `ms_tab`,`es_tab`,`ks_tab`,`rooted_eval`,`p`,`d`,`q8`,`raw_slots`,`sites`,`unused`,
     `a`,`e`,`sf`,`tf`,`inc`,`entry`,`order`,`res`,`nrest`,
     `bb`,`bt`,`ps`,`xs`,`ys`,`order_row`,`hin`,`h0`,`be`,`hbe`,
     `num_done`,`OK post`,`rest`,`ms`,`ks`,`fuel`,`gs`,`tail`,`u`]
    dft_packet_closed_row_key_success) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    DISJ1_TAC >> first_assum ACCEPT_TAC) >>
  disch_then (SUBST1_TAC o SYM) >>
  AP_TERM_TAC >> AP_TERM_TAC >>
  irule native_trace_block_suffix_cong >> simp[DROP_APPEND]
QED

Finalise request_cut_packet_closed_row_keys
