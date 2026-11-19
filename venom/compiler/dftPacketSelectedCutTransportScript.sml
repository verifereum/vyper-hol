Theory dftPacketSelectedCutTransport
Ancestors
  dftPacketNestedCutPrefix dftGasFromListTraceDefs dftGasInvCrossingProbe
  finite_map list rich_list

(* The aggregate in a selected call cell is the FINAL child aggregate.
   Nothing is required of cells or calls not selected by this cut. *)
Theorem dft_packet_selected_cut_prefix:
  !(acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (tab : (((num # num) list # num), 'a list list) fmap) old_tab cuts agg.
    cuts <> [] /\
    FST (HD cuts) = [] /\
    agg = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    (!i ai ds ei qi zi.
      i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      ?sf tf inc entry order res nrest later row.
        FLOOKUP acts ai = SOME (sf,tf,inc,entry,order,res,nrest) /\
        order = ds ++ ei::later /\ FLOOKUP tab (ai,ei) = SOME row /\
        qi <= LENGTH row /\
        (SUC i < LENGTH cuts ==>
          qi < LENGTH row /\
          EL qi row = agg (FST (EL (SUC i) cuts))) /\
        FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
          FLAT (TAKE qi row) =
        FLAT (MAP (\f. FLAT (THE (FLOOKUP old_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP old_tab (ai,ei))))) ==>
    ?rest. agg [] = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP old_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP old_tab (ai,ei))))) cuts) ++ rest
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `MAP piece cuts` >>
  `?rest. agg (FST (EL 0 cuts)) =
      FLAT (GENLIST (\i. piece (EL i cuts)) (LENGTH cuts)) ++ rest` by
    (qspecl_then [`LENGTH cuts`, `\i. agg (FST (EL i cuts))`,
        `\i. piece (EL i cuts)`] mp_tac dft_packet_nested_cut_prefix >>
     pure_rewrite_tac[BETA_THM] >> (impl_tac >-
       (conj_tac >- (Cases_on `cuts` >> gvs[]) >>
     qx_gen_tac `i` >> strip_tac >>
     `?ai ds ei qi zi. EL i cuts = (ai,ds,ei,qi,zi)` by
       metis_tac[pairTheory.PAIR] >>
     qpat_x_assum `!i ai ds ei qi zi. _` drule_all >> strip_tac >>
     `agg ai = FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
         FLAT row ++ FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) later)` by
       simp[MAP_APPEND,FLAT_APPEND] >>
     `piece (ai,ds,ei,qi,zi) =
        FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
          FLAT (TAKE qi row)` by simp[Abbr `piece`] >>
     Cases_on `SUC i < LENGTH cuts`
     >- (`FLAT row = FLAT (TAKE qi row) ++ EL qi row ++
             FLAT (DROP (SUC qi) row)` by
           (`row = TAKE qi row ++ [EL qi row] ++ DROP (SUC qi) row` by
              metis_tac[TAKE_DROP_SUC] >>
            pop_assum (fn th => CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV th)))) >>
            simp[FLAT_APPEND]) >>
         qexists_tac `FLAT (DROP (SUC qi) row) ++
           FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) later)` >>
         qpat_x_assum `agg = _` kall_tac >>
         simp[APPEND_ASSOC]) >>
     qexists_tac `FLAT (DROP qi row) ++
       FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) later)` >>
     `FLAT row = FLAT (TAKE qi row) ++ FLAT (DROP qi row)` by
       (qspecl_then [`qi`,`row`] (fn th =>
          CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV (GSYM th))))) TAKE_DROP >>
        simp[FLAT_APPEND]) >>
     qpat_x_assum `agg = _` kall_tac >>
     simp[APPEND_ASSOC])) >> simp[]) >>
  `GENLIST (\i. piece (EL i cuts)) (LENGTH cuts) = MAP piece cuts` by
    (irule LIST_EQ >> simp[EL_MAP,EL_GENLIST]) >>
  gvs[EL,HD]
QED

(* Extending a cut adds the fresh row prefix when the old selections agree. *)
Theorem dft_packet_extend_selected_cut_rows:
  FLOOKUP new_tab (path,depth) = SOME row /\
  (!i a ds e k z. i < LENGTH cuts /\ EL i cuts = (a,ds,e,k,z) ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP new_tab (a,f)))) ds) ++
      FLAT (TAKE k (THE (FLOOKUP new_tab (a,e)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP old_tab (a,f)))) ds) ++
      FLAT (TAKE k (THE (FLOOKUP old_tab (a,e))))) ==>
  FLAT (MAP (\(a,ds,e,k,z). FLAT (MAP
    (\f. FLAT (THE (FLOOKUP old_tab (a,f)))) ds) ++
      FLAT (TAKE k (THE (FLOOKUP old_tab (a,e))))) cuts) ++
    FLAT (TAKE cut_count row) =
  FLAT (MAP (\(a,ds,e,k,z). FLAT (MAP
    (\f. FLAT (THE (FLOOKUP new_tab (a,f)))) ds) ++
      FLAT (TAKE k (THE (FLOOKUP new_tab (a,e)))))
    (cuts ++ [(path,[],depth,cut_count,code)]))
Proof
  strip_tac >> simp[MAP_APPEND,FLAT_APPEND,APPEND_11] >>
  AP_TERM_TAC >>
  irule LIST_EQ >> simp[NoAsms,EL_MAP] >> qx_gen_tac `i` >> strip_tac >>
  Cases_on `EL i cuts` >> rename1 `EL i cuts = (a,fields)` >>
  PairCases_on `fields` >> simp[] >> metis_tac[]
QED

(* Historical cuts frame only their selected nonterminal edge.  In particular,
   no call record is framed at the terminal cut, where a new call may be added.
   Mutable activation results and row cursors are allowed to change. *)
Theorem dft_packet_selected_cut_transport:
  !(acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
   (blocks : (((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
   (calls : (gas_event, num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap).

  (!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    (!sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
        ini hi bei counti fronti closedi resti.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) ==>
      ?order' res' nrest' count' front' closed' rest' later'.
        FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,order',res',nrest') /\
        FLOOKUP blocks' (ai,ei) =
          SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,count',front',closed',rest') /\
        order' = ds ++ ei::later') /\
    (!f. MEM f ds ==>
      FST (THE (FLOOKUP blocks' (ai,f))) = FST (THE (FLOOKUP blocks (ai,f)))) /\
    (SUC i < LENGTH cuts ==>
      !cid. EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai ==>
        FLOOKUP calls' (ai,ei,cid) = FLOOKUP calls (ai,ei,cid)) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei)))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei)))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) /\
  (?mr'. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab' ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Mcut ++ mr') /\
  (?er'. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab' ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Ecut ++ er') /\
  (?kr'. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab' ([],e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Kcut ++ kr') /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
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
        ai = a /\ ei = e /\ qi = q /\ zi = z
       else
        ?cid h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
      EL i levels =
        (sfi, MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
          [(bbi,ei,zi)], if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
  Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
  Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
  LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
  (!F gs tail.
    N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
    levels_ok F C7 levels
      (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
      (MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts ai))))) cuts)
      root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
    (?extra. Ecut = FST (rooted_eval F C7 levels
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
      OK u =>
        FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
        u.vs_gas_readings = tail /\
        (?before after.
          dftGasFromListTraceDefs$trace_blocks [] 0 F C7 root_sf
            (root_entry with vs_gas_readings := gs ++ tail) =
            before ++ [((a,e,(EL (LENGTH z)
              (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
              EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
          dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
        (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
          (Ecut,OK (u with vs_gas_readings := tail'))) /\
        (body_entry = NONE ==> u with vs_gas_readings := st.vs_gas_readings = st) /\
        (a = p /\ e = d /\ IS_SOME body_entry /\
          inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
          (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op st) /\
          u.vs_initial_fmp = st.vs_initial_fmp)
    | stopped =>
        run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
        gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
          FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)))) ==>
  ?mr' er' kr'.
    MAP (\(ai,ds,ei,qi,zi). ai) cuts =
      REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
    LENGTH cuts = LENGTH levels /\
    (!i ai ds ei qi zi.
      i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
        ini hi bei counti fronti closedi resti later.
        FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
        FLOOKUP blocks' (ai,ei) =
          SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
        orderi = ds ++ ei::later /\
        (if SUC i = LENGTH cuts then
          ai = a /\ ei = e /\ qi = q /\ zi = z
         else
          ?cid h b0 done_at_call child_entry ret.
            EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
            FLOOKUP calls' (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
            qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
            zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
            EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
            (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
        EL i levels =
          (sfi, MAP (\f. (FST (THE (FLOOKUP blocks' (ai,f))),f,
            DROP (phi_prefix_length (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)
              (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)) ds ++
            [(bbi,ei,zi)], if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
    Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei))))) cuts) /\
    Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei))))) cuts) /\
    Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei))))) cuts) /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab' ([],e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Mcut ++ mr' /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab' ([],e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Ecut ++ er' /\
    FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab' ([],e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts' [])))))))) = Kcut ++ kr' /\
    LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
    (!F gs tail.
      N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
      levels_ok F C7 levels
        (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
        (MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts' ai))))) cuts)
        root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
      (?extra. Ecut = FST (rooted_eval F C7 levels
        (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
      (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
        OK u =>
          FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
          u.vs_gas_readings = tail /\
          (?before after.
            dftGasFromListTraceDefs$trace_blocks [] 0 F C7 root_sf
              (root_entry with vs_gas_readings := gs ++ tail) =
              before ++ [((a,e,(EL (LENGTH z)
                (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
            dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
          (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
            (Ecut,OK (u with vs_gas_readings := tail'))) /\
          (body_entry = NONE ==> u with vs_gas_readings := st.vs_gas_readings = st) /\
          (a = p /\ e = d /\ IS_SOME body_entry /\
            inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
            (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op st) /\
            u.vs_initial_fmp = st.vs_initial_fmp)
      | stopped =>
          run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
          gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))
Proof
  rpt gen_tac >> strip_tac >> qexistsl_tac [`mr'`,`er'`,`kr'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "description" >>
  conj_tac >- suspend "masks" >>
  conj_tac >- suspend "sites" >>
  conj_tac >- suspend "keys" >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "semantics"
QED

Resume dft_packet_selected_cut_transport[description]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!i ai ds ei qi zi. _ ==> (_ /\ _ /\ _ /\ _ /\ _ /\ _)`,
     `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i ai ds ei qi zi. _ ==> (_ /\ _ /\ _ /\ _ /\ _ /\ _)` drule_all >> strip_tac >>
  qpat_x_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
    drule_all >> strip_tac >>
  qpat_x_assum `!sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti. _`
    drule_all >> strip_tac >>
  `MAP (\f. (FST (THE (FLOOKUP blocks' (ai,f))),f,
      DROP (phi_prefix_length (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)
        (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)) ds =
    MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
      DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds` by
    (irule MAP_CONG >> simp[]) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  asm_rewrite_tac[] >>
  Cases_on `SUC i = LENGTH cuts` >- gvs[] >>
  `SUC i < LENGTH cuts` by decide_tac >>
  gvs[] >> goal_assum (drule_at Any) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> metis_tac[]
QED

Resume dft_packet_selected_cut_transport[masks]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!i ai ds ei qi zi. _ ==> (_ /\ _ /\ _ /\ _ /\ _ /\ _)`,`Mcut = FLAT _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  qpat_x_assum `Mcut = _` SUBST1_TAC >> AP_TERM_TAC >>
  irule MAP_CONG >> simp[] >> gen_tac >> PairCases_on `x` >> simp[] >>
  strip_tac >> metis_tac[MEM_EL]
QED
Resume dft_packet_selected_cut_transport[sites]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!i ai ds ei qi zi. _ ==> (_ /\ _ /\ _ /\ _ /\ _ /\ _)`,`Ecut = FLAT _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  qpat_x_assum `Ecut = _` SUBST1_TAC >> AP_TERM_TAC >>
  irule MAP_CONG >> simp[] >> gen_tac >> PairCases_on `x` >> simp[] >>
  strip_tac >> metis_tac[MEM_EL]
QED
Resume dft_packet_selected_cut_transport[keys]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!i ai ds ei qi zi. _ ==> (_ /\ _ /\ _ /\ _ /\ _ /\ _)`,`Kcut = FLAT _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  qpat_x_assum `Kcut = _` SUBST1_TAC >> AP_TERM_TAC >>
  irule MAP_CONG >> simp[] >> gen_tac >> PairCases_on `x` >> simp[] >>
  strip_tac >> metis_tac[MEM_EL]
QED
Resume dft_packet_selected_cut_transport[semantics]:
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!i ai ds ei qi zi. _ ==> (_ /\ _ /\ _ /\ _ /\ _ /\ _)`,
     `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`,
     `!F gs tail. N <= F /\ LIST_REL _ Mcut gs ==> _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  `MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts' ai))))) cuts =
    MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts ai))))) cuts` by
    (irule MAP_CONG >> simp[] >> gen_tac >> PairCases_on `x` >> simp[] >>
     strip_tac >> drule (iffLR MEM_EL) >> strip_tac >>
     qpat_x_assum `_ = EL _ cuts` (assume_tac o SYM) >>
     qpat_assum `!i ai ds ei qi zi. _ ==> (_ /\ _ /\ _ /\ _ /\ _ /\ _)` drule_all >> strip_tac >>
     qpat_x_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later. _`
       drule_all >> strip_tac >>
     qpat_x_assum `!sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti. _`
       drule_all >> strip_tac >> simp[]) >>
  asm_rewrite_tac[]
QED
Finalise dft_packet_selected_cut_transport
