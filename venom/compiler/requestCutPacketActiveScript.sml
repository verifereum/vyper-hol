Theory requestCutPacketActive
Ancestors
  requestCutPacketBody requestCutPacketExecution requestCutNativeBoundary
  dftFinitePacket dftPacketEntryReplay dftPacketInvokePrefixStop
  dftRunRel dftGasFromListTraceDefs dftIndexedExec dftGasFromListReadings
  venomExecSemantics venomExecProofs venomInst venomState
  finite_map list rich_list arithmetic

Theorem request_cut_packet_active_body:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    ds later bb bt ps xs ys row_order hin h0 be hbe done front closed brest ms ks
    fuel k kgss tail z v.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    order = ds ++ e::later /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,row_order,hin,h0,SOME (be,hbe),done,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
    N <= fuel /\ 0 < e /\ k <= LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE done row_order)) /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE k xs /\
    v = hin with vs_gas_readings := FLAT kgss ++ tail ==>
    ?sp. eval_phis v bb.bb_instructions = OK sp /\
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
            FLAT (TAKE k ks) ++ MAP FST (trace_gas (trace_block a e (fuel-e) C7 sf bb u))
      | stopped => ~(?ir u. stopped = IntRet ir u) /\
          run_blocks (SUC (fuel-e)) C7 sf v = stopped /\
          ?extra. FLAT (TAKE k ks) =
            MAP FST (trace_gas (trace_blocks a (e-1) (SUC (fuel-e)) C7 sf v)) ++ extra)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb` by suspend "lookup" >>
  drule_all dft_packet_selected_order_entries >> strip_tac >>
  `?sp7. eval_phis v bb.bb_instructions = OK sp7 /\
    FOLDR (dft_exec_cons (fuel-e) C7) OK
      (DROP (phi_prefix_length bb.bb_instructions) ps)
      (sp7 with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      OK (be with vs_gas_readings := FLAT kgss ++ tail)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`v = _`,`bb.bb_instructions = ps ++ xs`,`EVERY (\i. is_pseudo i.inst_opcode) ps`,
        `EVERY (\i. ~is_pseudo i.inst_opcode) xs`,`EVERY (\i. ~is_pseudo i.inst_opcode) ys`,
        `eval_phis hin (ps ++ ys) = OK _`,`FOLDR (dft_exec_cons (fuel-e) C8) OK _ _ = OK be`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all dft_packet_body_entry_replay >> simp[]) >>
  `phi_prefix_length bb.bb_instructions <= LENGTH ps` by
    (`EVERY (\i. i.inst_opcode <> PHI) xs` by
       (qpat_assum `EVERY (\i. ~is_pseudo i.inst_opcode) xs` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
     simp[dft_phi_prefix_append,phi_prefix_length_le]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
      (DROP (phi_prefix_length bb.bb_instructions) ps)` by
    (irule EVERY_DROP >> qpat_assum `EVERY (\i. is_pseudo i.inst_opcode) ps` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM] >>
     strip_tac >> qx_gen_tac `i` >> strip_tac >> first_x_assum (drule_then mp_tac) >>
     Cases_on `i.inst_opcode` >> simp[is_pseudo_def,is_terminator_def]) >>
  `lookup_block v.vs_current_bb sf.fn_blocks = SOME bb` by simp[] >>
  qexists_tac `sp7` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  `FOLDR (dft_exec_cons (fuel-e) C7) OK z
    (sp7 with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
    FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs)
      (be with vs_gas_readings := FLAT kgss ++ tail)` by
    (qpat_assum `z = _` (fn th => rewrite_tac[th,FOLDR_APPEND]) >>
     simp[Once dft_exec_prefix_continue]) >>
  pop_assum (fn th => rewrite_tac [th]) >>
  mp_tac (Q.SPECL [`bb`,`ps`,`xs`,
    `sp7 with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
    `be with vs_gas_readings := FLAT kgss ++ tail`]
    (Q.INST [`f` |-> `fuel-e`, `C` |-> `C7`, `p` |-> `a`, `d` |-> `e`, `sf` |-> `sf`]
      request_cut_native_body_projection)) >>
  impl_tac >- (simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  drule_all request_cut_packet_body_keys >>
  disch_then (qspec_then `tail` mp_tac) >>
  Cases_on `FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs)
    (be with vs_gas_readings := FLAT kgss ++ tail)` >>
  simp[NoAsms] >> strip_tac
  >- suspend "success" >>
  `!ir u. FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs)
    (be with vs_gas_readings := FLAT kgss ++ tail) <> IntRet ir u` by
    (irule dft_packet_nonterminator_prefix_no_intret >> first_assum ACCEPT_TAC) >>
  TRY
    (qpat_assum `FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs) _ = IntRet _ _`
       (fn eq => qpat_assum `!ir u. FOLDR _ _ _ _ <> IntRet ir u`
         (mp_tac o REWRITE_RULE [eq])) >> simp[NoAsms]) >>
  `~(?u. FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs)
    (be with vs_gas_readings := FLAT kgss ++ tail) = OK u)` by
    (qpat_assum `FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs) _ = _`
      (fn th => simp[NoAsms,th])) >>
  `SUC (e-1) = e` by decide_tac >>
  `run_blocks (SUC (fuel-e)) C7 sf v =
      FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) /\
    trace_gas (trace_blocks a (e-1) (SUC (fuel-e)) C7 sf v) =
      trace_gas (trace_block a e (fuel-e) C7 sf bb
        (sp7 with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
    (`exec_block (fuel-e) C7 bb (sp7 with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
        FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail)` by
       asm_rewrite_tac[] >>
     mp_tac (Q.INST [`s` |-> `v`, `f` |-> `fuel-e`, `C` |-> `C7`,
       `sp` |-> `sp7`, `d` |-> `e-1`,
       `r` |-> `FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs)
         (be with vs_gas_readings := FLAT kgss ++ tail)`]
       request_cut_native_block_stopped) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `SUC (e-1) = e` (fn th => simp[NoAsms,th])) >>
  asm_rewrite_tac[] >>
  qexists_tac `extra` >> asm_rewrite_tac[]
QED

Resume request_cut_packet_active_body[lookup]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a e bb bt ps xs ys row_order in_state h0 bentry count front closed brest.
     FLOOKUP blocks (a,e) = _ ==> _`
    (fn rows => qpat_assum `FLOOKUP blocks (a,e) = SOME _`
      (strip_assume_tac o MATCH_MP rows)) >>
  qpat_x_assum `lookup_block hin.vs_current_bb _.fn_blocks = _` mp_tac >>
  qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
    (fn lookup => qpat_x_assum `FLOOKUP acts a = SOME _`
      (mp_tac o REWRITE_RULE [lookup,optionTheory.SOME_11,pairTheory.PAIR_EQ])) >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]
QED

Resume request_cut_packet_active_body[success]:
  simp[]
QED

Finalise request_cut_packet_active_body
