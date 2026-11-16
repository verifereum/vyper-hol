Theory gasFocusPacketRows
Ancestors
  dftFinitePacket finite_map pred_set list arithmetic

Theorem dft_focus_packet_row_occurrence:
  dft_focus_packet_rel (N:num) C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  (a,e) IN FDOM blocks ==>
  ?i cid tf inst st.
    i <= FST packet /\
    EL i (dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry) =
      ((a,e,cid),tf,inst,st)
Proof
  strip_tac >>
  `?row. FLOOKUP blocks (a,e) = SOME row` by simp[FLOOKUP_DEF] >>
  PairCases_on `row` >>
  qpat_x_assum `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    mp_tac >>
  pure_rewrite_tac [dft_focus_packet_rel_def] >> strip_tac >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,count,front,closed,brest) ==> _`
    (qspecl_then [`a`,`e`] mp_tac) >> disch_then drule >>
  strip_tac >> qexists_tac `row7` >> simp[] >>
  qpat_x_assum `EL row7 _ = _` (irule_at Any)
QED

Theorem dft_focus_packet_rows_bound:
  dft_focus_packet_rel (N:num) C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused ==>
  CARD (FDOM blocks) <= SUC (FST packet)
Proof
  strip_tac >>
  qabbrev_tac `tr = dftGasFromListTraceDefs$trace_blocks [] 0 N C8 root_tf root_entry` >>
  qabbrev_tac `key = \i. (FST (FST (EL i tr)), FST (SND (FST (EL i tr))))` >>
  `FDOM blocks SUBSET IMAGE key (count (SUC (FST packet)))` by
    (rw[SUBSET_DEF] >> PairCases_on `x` >>
     drule_all dft_focus_packet_row_occurrence >> strip_tac >>
     simp[IN_IMAGE] >> qexists_tac `i` >>
     simp[Abbr `key`, Abbr `tr`]) >>
  `CARD (FDOM blocks) <= CARD (IMAGE key (count (SUC (FST packet))))` by
    (irule CARD_SUBSET >> simp[]) >>
  `CARD (IMAGE key (count (SUC (FST packet)))) <= SUC (FST packet)` by
    (irule LESS_EQ_TRANS >>
     qexists_tac `CARD (count (SUC (FST packet)))` >>
     conj_tac >- (irule CARD_IMAGE >> simp[]) >> simp[]) >>
  decide_tac
QED
