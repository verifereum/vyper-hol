Theory requestCutPacketBody
Ancestors
  requestCutNativePartial dftFinitePacket dftPacketClosedRowNative
  dftGasFromListTraceDefs dftIndexedExec venomExecSemantics venomInst venomState
  passSimulationDefs list rich_list arithmetic finite_map

Theorem request_cut_packet_body_keys:
  !N C7 C8 root_sf root_tf root_entry packet acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys row_order hin h0 be hbe done front closed brest ms ks fuel k kgss tail.
    dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
      acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,row_order,hin,h0,SOME (be,hbe),done,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
    N <= fuel /\ k <= LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE done row_order)) /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
    case FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs)
           (be with vs_gas_readings := FLAT kgss ++ tail) of
      OK u => u.vs_inst_idx = LENGTH ps + k /\ u.vs_gas_readings = tail /\
        exec_block (fuel-e) C7 bb (be with vs_gas_readings := FLAT kgss ++ tail) =
          exec_block (fuel-e) C7 bb u /\
        MAP FST (trace_gas (trace_block a e (fuel-e) C7 sf bb
          (be with vs_gas_readings := FLAT kgss ++ tail))) =
          FLAT (TAKE k ks) ++ MAP FST (trace_gas (trace_block a e (fuel-e) C7 sf bb u))
    | stopped =>
        exec_block (fuel-e) C7 bb (be with vs_gas_readings := FLAT kgss ++ tail) = stopped /\
        ?extra. FLAT (TAKE k ks) = MAP FST (trace_gas (trace_block a e (fuel-e) C7 sf bb
          (be with vs_gas_readings := FLAT kgss ++ tail))) ++ extra
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_instructions = ps ++ xs /\ be.vs_inst_idx = LENGTH ps /\
    LENGTH (FLAT (TAKE k ks)) = LENGTH (FLAT kgss) /\
    (!u. FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs)
       (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
       u.vs_gas_readings = tail /\
       trace_gas (trace_block a e (fuel-e) C7 sf
         (bb with bb_instructions := TAKE (LENGTH ps+k) bb.bb_instructions)
         (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss))` by
    suspend "row_data" >>
  `?extra. FLAT (TAKE k ks) = MAP FST (trace_gas
    (trace_block a e (fuel-e) C7 sf
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
      (be with vs_gas_readings := FLAT kgss ++ tail))) ++ extra` by
    (irule dft_packet_row_cut_keys >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     map_every (fn pat => qpat_assum pat (irule_at Any))
       [`FLOOKUP acts a = _`,`FLOOKUP blocks (a,e) = _`,
        `FLOOKUP ms_tab (a,e) = _`,`FLOOKUP ks_tab (a,e) = _`] >>
     simp[]) >>
  `trace_block a e (fuel-e) C7 sf
      (bb with bb_instructions := TAKE (LENGTH ps+k) bb.bb_instructions)
      (be with vs_gas_readings := FLAT kgss ++ tail) =
    trace_block a e (fuel-e) C7 sf
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
      (be with vs_gas_readings := FLAT kgss ++ tail)` by
    (irule native_trace_block_suffix_cong >>
     simp[TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG]) >>
  mp_tac (Q.SPECL [`k`,`be with vs_gas_readings := FLAT kgss ++ tail`,`bb`,`FLAT (TAKE k ks)`]
    (Q.INST [`f` |-> `fuel-e`,`C` |-> `C7`,`sf` |-> `sf`,`p` |-> `a`,`d` |-> `e`]
      request_cut_native_partial_row)) >>
  impl_tac >- suspend "native_premises" >>
  Cases_on `FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE k xs)
    (be with vs_gas_readings := FLAT kgss ++ tail)` >>
  simp[DROP_APPEND,ADD_COMM] >>
  metis_tac[]
QED

Resume request_cut_packet_body_keys[row_data]:
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a e bb bt ps xs ys order_row in_state h0 bentry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (fn row => qpat_assum `FLOOKUP blocks (a,e) = SOME _`
      (strip_assume_tac o MATCH_MP row)) >>
  qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
    (fn lookup => qpat_x_assum `FLOOKUP acts a = SOME _`
      (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o
       REWRITE_RULE [lookup,optionTheory.SOME_11,pairTheory.PAIR_EQ])) >>
  qpat_x_assum `case SOME (be,hbe) of NONE => _ | SOME v => _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
    (qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
  qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
     FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
     FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _`
    (drule_all_then (fn th =>
      (assume_tac (cj 5 th) >>
       qpat_assum `FLOOKUP acts a = SOME _`
         (assume_tac o CONJUNCT2 o MATCH_MP (cj 7 th))))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `_.vs_inst_idx = LENGTH _` mp_tac >> simp[]) >>
  conj_tac
  >- (qpat_assum `LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks`
        (mp_tac o Q.SPEC `k` o MATCH_MP LIST_REL_TAKE) >>
      qpat_assum `LIST_REL (LIST_REL _) (TAKE k ms) kgss` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      `LIST_REL (\m ws. LENGTH m = LENGTH ws) (TAKE k ms) kgss` by
        (irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[LIST_REL_EL_EQN]) >>
      `MAP LENGTH (TAKE k ms) = MAP LENGTH (TAKE k ks) /\
       MAP LENGTH (TAKE k ms) = MAP LENGTH kgss` by metis_tac[MAP_EQ_LIST_REL, LIST_REL_LENGTH] >>
      `MAP LENGTH (TAKE k ks) = MAP LENGTH kgss` by metis_tac[] >>
      simp[LENGTH_FLAT]) >>
  qpat_x_assum `!F j fillings suffix. N <= F /\ _ ==> _`
    (qspecl_then [`fuel`,`k`,`kgss`,`tail`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> gen_tac >>
  first_x_assum (qspec_then `u` mp_tac) >>
  qpat_assum `be.vs_inst_idx = LENGTH ps` (fn th => simp[NoAsms,th])
QED

Resume request_cut_packet_body_keys[native_premises]:
  `DROP be.vs_inst_idx bb.bb_instructions = xs` by simp[DROP_APPEND] >>
  qpat_assum `DROP be.vs_inst_idx bb.bb_instructions = xs` (fn th => simp[NoAsms,th]) >>
  qpat_assum `be.vs_inst_idx = LENGTH ps` (fn th => simp[NoAsms,th]) >>
  rpt conj_tac
  >- simp[]
  >- first_assum ACCEPT_TAC
  >- (qexists_tac `extra` >> PURE_ONCE_REWRITE_TAC [ADD_COMM] >>
      qpat_assum `trace_block a e (fuel-e) C7 sf (bb with bb_instructions := _) _ = _`
        (fn th => REWRITE_TAC[th]) >>
      first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!u. _ = OK u ==> _` (drule_then strip_assume_tac) >>
  PURE_ONCE_REWRITE_TAC [ADD_COMM] >>
  qpat_assum `trace_gas _ = ZIP _` SUBST1_TAC >>
  qpat_assum `LENGTH (FLAT (TAKE k ks)) = LENGTH (FLAT kgss)`
    (fn th => simp[NoAsms, MAP_ZIP, th])
QED

Finalise request_cut_packet_body_keys
