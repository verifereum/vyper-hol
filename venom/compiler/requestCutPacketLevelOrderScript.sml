Theory requestCutPacketLevelOrder
Ancestors
  dftFinitePacket venomState list rich_list finite_map arithmetic

Theorem request_cut_packet_level_position:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  order = ds ++ e::later ==>
  e = inc + SUC (LENGTH ds) /\ e <= N /\
  inc = (case a of [] => 0 | (depth,cid)::parent => depth) /\
  (?row. FLOOKUP blocks (a,e) = SOME row) /\
  (?ms. FLOOKUP ms_tab (a,e) = SOME ms) /\
  (?ks. FLOOKUP ks_tab (a,e) = SOME ks)
Proof
  strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
    (fn info => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
      (strip_assume_tac o MATCH_MP info)) >>
  `e = inc + SUC (LENGTH ds)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`order = ds ++ e::later`,`order = GENLIST _ _`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `LENGTH ds < LENGTH order` by simp[] >>
     `EL (LENGTH ds) order = inc + SUC (LENGTH ds)` by
       (qpat_assum `order = GENLIST _ _` (fn th => once_rewrite_tac[th]) >>
        simp[EL_GENLIST]) >>
     qpat_assum `order = ds ++ e::later` (fn th => fs[th,EL_APPEND_EQN])) >>
  `(a,e) IN FDOM blocks` by
    (qpat_assum `!e. MEM e order <=> (a,e) IN FDOM blocks` (qspec_then `e` mp_tac) >>
     qpat_assum `order = ds ++ e::later` (fn th => simp[NoAsms,th])) >>
  `?row. FLOOKUP blocks (a,e) = SOME row` by
    (qpat_assum `(a,e) IN FDOM blocks` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]) >>
  PairCases_on `row` >>
  qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _`
    (fn info => qpat_assum `FLOOKUP blocks (a,e) = SOME _`
      (strip_assume_tac o MATCH_MP info)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`(a,e) IN FDOM blocks`,`FDOM blocks = FDOM ms_tab`,`FDOM blocks = FDOM ks_tab`] >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[FLOOKUP_DEF,optionTheory.NOT_NONE_SOME]
QED

Theorem request_cut_packet_root_activation:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused ==>
  ?order. FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)
Proof
  strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qexists_tac `order` >> first_assum ACCEPT_TAC
QED
