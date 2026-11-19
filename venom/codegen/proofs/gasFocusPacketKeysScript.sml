Theory gasFocusPacketKeys
Ancestors
  dftFinitePacket finite_map list rich_list arithmetic

Theorem dft_focus_packet_activation_key_origin:
  dft_focus_packet_rel (N:num) C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  MEM key (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e)))) order)) ==>
  ?a' e bb bt ps xs ys rho in_state h0 body_entry count front closed brest r.
    FLOOKUP blocks (a',e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
    r < LENGTH xs /\ (EL r xs).inst_opcode = GAS /\
    key = (a',e,(EL r xs).inst_id)
Proof
  rewrite_tac[GSYM AND_IMP_INTRO] >> disch_tac >>
  qpat_x_assum `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _` mp_tac >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = _ ==> _` mp_tac >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\
    FLOOKUP es_tab (a,e) = _ /\ FLOOKUP ks_tab (a,e) = _ ==> _` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM ms_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM es_tab` mp_tac >>
  qpat_x_assum `FDOM blocks = FDOM ks_tab` mp_tac >>
  qpat_x_assum `AK = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> ntac 8 disch_tac >>
  map_every qid_spec_tac [`key`,`nrest`,`res`,`order`,`entry`,`tf`,`sf`,`a`,`inc`] >>
  measureInduct_on `N-inc` >> rpt strip_tac >>
  qpat_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = _ ==> _` (drule o cj 6) >> disch_tac >>
  qpat_x_assum `!a sf tf inc entry order res nrest.
    FLOOKUP acts a = _ ==> _` (drule o cj 7) >> disch_tac >>
  qpat_x_assum `MEM key _` mp_tac >>
  simp[MEM_FLAT,MEM_MAP,PULL_EXISTS] >> rpt strip_tac >>
  rename1 `MEM e order` >>
  `(a,e) IN FDOM blocks` by metis_tac[] >>
  Cases_on `FLOOKUP blocks (a,e)` >- gvs[FLOOKUP_DEF] >>
  rename1 `FLOOKUP blocks (a,e) = SOME row` >> PairCases_on `row` >>
  rename1 `FLOOKUP blocks (a,e) =
    SOME (row_bb,row_bt,row_ps,src,tgt,row_rho,row_state,row_h,row_body,
          row_count,row_front,row_closed,row_rest)` >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = _ ==> _` drule >> strip_tac >>
  Cases_on `row_body`
  >- (qpat_x_assum `case NONE of NONE => _ | SOME v => _` mp_tac >>
      simp[] >> strip_tac >> gvs[]) >>
  rename1 `FLOOKUP blocks (a,e) =
    SOME (row_bb,row_bt,row_ps,src,tgt,row_rho,row_state,row_h,SOME be_pair,
          row_count,row_front,row_closed,row_rest)` >>
  PairCases_on `be_pair` >>
  Cases_on `FLOOKUP ms_tab (a,e)` >- gvs[FLOOKUP_DEF] >>
  Cases_on `FLOOKUP es_tab (a,e)` >- gvs[FLOOKUP_DEF] >>
  Cases_on `FLOOKUP ks_tab (a,e)` >- gvs[FLOOKUP_DEF] >>
  rename1 `FLOOKUP ks_tab (a,e) = SOME ks` >>
  qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    _ ==> _` drule_all >> strip_tac >>
  qpat_x_assum `!sf tf inc entry order res nrest. _ ==> _`
    (drule o cj 1) >> disch_tac >>
  `?r. r < LENGTH ks /\ l = EL r ks` by metis_tac[MEM_EL,optionTheory.THE_DEF] >>
  gvs[] >>
  rename1 `r < LENGTH xs` >>
  qpat_x_assum `!q. q < LENGTH xs ==> _` (qspec_then `r` mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `(EL r src).inst_opcode = GAS ==> _` >>
  `MEM e order` by metis_tac[] >>
  `inc < e` by
    (`MEM e (GENLIST (\i. inc + SUC i) (LENGTH order))` by metis_tac[] >>
     gvs[MEM_GENLIST]) >>
  `N-e < N-inc` by decide_tac >>
  Cases_on `(EL r src).inst_opcode = GAS`
  >- (gvs[] >> goal_assum (drule_at Any) >> simp[]) >>
  reverse (Cases_on `(EL r src).inst_opcode = INVOKE`) >- gvs[] >>
  qpat_x_assum `_ = INVOKE ==> _` mp_tac >> simp[] >>
  Cases_on `FLOOKUP calls (a,e,(EL r src).inst_id)` >- (strip_tac >> gvs[]) >>
  strip_tac >> rename1 `FLOOKUP calls (a,e,_) = SOME cr` >> PairCases_on `cr` >>
  qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = _ ==> _` drule >> strip_tac >>
  qpat_x_assum `!y. _ ==> !a sf tf entry order res nrest key. _`
    (qspec_then `e` mp_tac) >>
  (impl_tac >- decide_tac) >> disch_then drule >> gvs[]
QED

Theorem dft_focus_packet_root_key_origin:
  dft_focus_packet_rel (N:num) C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE) /\
  MEM key (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab ([],e)))) order)) ==>
  ?a' e bb bt ps xs ys rho in_state h0 body_entry count front closed brest r.
    FLOOKUP blocks (a',e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
    r < LENGTH xs /\ (EL r xs).inst_opcode = GAS /\
    key = (a',e,(EL r xs).inst_id)
Proof
  metis_tac[dft_focus_packet_activation_key_origin]
QED
