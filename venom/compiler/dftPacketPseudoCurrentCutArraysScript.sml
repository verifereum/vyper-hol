Theory dftPacketPseudoCurrentCutArrays
Ancestors
  dftPacketSelectedCutTransport finite_map list rich_list arithmetic

(* Only the terminal tuple changes. Earlier pieces use strict prefixes of the
   selected call cells; those cells themselves supply the final child payload. *)
Theorem pseudo_current_cut_array[local]:
  !(acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (calls : (gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (tab : (((num # num) list # num),'a list list) fmap) out agg
    (pre : ((num # num) list # num list # num # num # instruction list) list)
    p D d q z0 z1 c0 c1 row X0 X1.
    c0 = pre ++ [(p,D,d,0,z0)] /\
    c1 = pre ++ [(p,D,d,q,z1)] /\
    FST (HD c0) = [] /\
    FLOOKUP out (p,d) = SOME row /\ q <= LENGTH row /\
    agg = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP out (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    (!i ai ds ei qi zi.
      i < LENGTH c0 /\ EL i c0 = (ai,ds,ei,qi,zi) ==>
      ?sf tf inc entry order res nrest later.
        FLOOKUP acts ai = SOME (sf,tf,inc,entry,order,res,nrest) /\
        order = ds ++ ei::later /\
        (SUC i < LENGTH c0 ==>
          ?cid h b done ent ret.
            FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b,done,ent,ret) /\
            FST (EL (SUC i) c0) = (ei,cid)::ai)) /\
    (!i ai ds ei qi zi f.
      i < LENGTH c0 /\ EL i c0 = (ai,ds,ei,qi,zi) /\ MEM f ds ==>
      FLOOKUP out (ai,f) = FLOOKUP tab (ai,f)) /\
    (!a e cid n h b done ent ret.
      FLOOKUP calls (a,e,cid) = SOME (n,h,b,done,ent,ret) ==>
      TAKE n (THE (FLOOKUP out (a,e))) = TAKE n (THE (FLOOKUP tab (a,e))) /\
      ?r. FLOOKUP out (a,e) = SOME r /\ n < LENGTH r /\
        EL n r = agg ((e,cid)::a)) /\
    X0 = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP tab (ai,ei))))) c0) /\
    X1 = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP out (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP out (ai,ei))))) c1) ==>
    X1 = X0 ++ FLAT (TAKE q row) /\ ?rest. agg [] = X1 ++ rest
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. i < LENGTH pre ==> EL i c0 = EL i pre /\ EL i c1 = EL i pre` by
    simp[EL_APPEND1] >>
  `EL (LENGTH pre) c0 = (p,D,d,0,z0) /\
   EL (LENGTH pre) c1 = (p,D,d,q,z1)` by simp[EL_APPEND_EQN] >>
  `!i. i < LENGTH c1 ==> FST (EL i c1) = FST (EL i c0)` by
    (rpt strip_tac >> Cases_on `i < LENGTH pre` >- simp[] >>
     `i = LENGTH pre` by
       (`i <= LENGTH pre` by
          ((qpat_assum `i < LENGTH c1` mp_tac >> simp[LESS_EQ_IFF_LESS_SUC] >> (gvs[LESS_EQ_IFF_LESS_SUC]))) >>
        decide_tac) >> simp[EL_APPEND_EQN]) >>
  `FST (HD c1) = []` by
    (Cases_on `pre` >> gvs[]) >>
  `!ai ds ei qi zi. MEM (ai,ds,ei,qi,zi) pre ==>
    TAKE qi (THE (FLOOKUP out (ai,ei))) = TAKE qi (THE (FLOOKUP tab (ai,ei)))` by
    (rpt gen_tac >> simp[MEM_EL] >> disch_then (qx_choose_then `i` strip_assume_tac) >>
     `i < LENGTH c0 /\ EL i c0 = (ai,ds,ei,qi,zi)` by simp[] >>
     qpat_assum `!i ai ds ei qi zi. _ ==> ?sf tf inc entry order res nrest later. _`
       (drule_all_then strip_assume_tac) >>
     `SUC i < LENGTH c0` by simp[] >>
     first_x_assum (drule_then strip_assume_tac) >>
     qpat_assum `!a e cid n h b done ent ret. _` (drule_then strip_assume_tac) >>
     simp[]) >>
  `!i ai ds ei qi zi. i < LENGTH c0 /\ EL i c0 = (ai,ds,ei,qi,zi) ==>
    MAP (\f. FLAT (THE (FLOOKUP out (ai,f)))) ds =
    MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds` by
    (rpt strip_tac >> irule listTheory.MAP_CONG >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!i ai ds ei qi zi f. _` (drule_all_then assume_tac) >> simp[]) >>
  conj_tac
  >- suspend "flatten"
  >> suspend "prefix"
QED

Resume pseudo_current_cut_array[flatten]:
  simp[MAP_APPEND,FLAT_APPEND,APPEND_ASSOC] >>
  `MAP (\f. FLAT (THE (FLOOKUP out (p,f)))) D =
   MAP (\f. FLAT (THE (FLOOKUP tab (p,f)))) D` by
    (qpat_assum `!i ai ds ei qi zi. _ ==> MAP _ _ = MAP _ _`
       (qspecl_then [`LENGTH pre`,`p`,`D`,`d`,`0`,`z0`] mp_tac) >> simp[]) >>
  simp[] >>
  AP_TERM_TAC >>
  irule listTheory.MAP_CONG >> simp[] >>
  gen_tac >> PairCases_on `x` >> disch_tac >>
  qpat_assum `!ai ds ei qi zi. MEM _ pre ==> _` (drule_then assume_tac) >>
  qpat_assum `MEM _ pre` (qx_choose_then `i` strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  `i < LENGTH c0 /\ EL i c0 = (x0,x1,x2,x3,x4)` by simp[EL_APPEND1] >>
  qpat_assum `!i ai ds ei qi zi. _ ==> MAP _ _ = MAP _ _`
    (drule_all_then assume_tac) >> simp[]
QED

Resume pseudo_current_cut_array[prefix]:
  qpat_assum `X1 = _` (fn th => PURE_REWRITE_TAC [th]) >>
  irule dft_packet_selected_cut_prefix >>
  conj_tac >- simp[] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`acts`,`out`] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  Cases_on `i < LENGTH pre`
  >- ( `i < LENGTH c0 /\ EL i c0 = (ai,ds,ei,qi,zi) /\ SUC i < LENGTH c0` by gvs[EL_APPEND1] >>
       qpat_assum `!i ai ds ei qi zi. _ ==> ?sf tf inc entry order res nrest later. _`
         (drule_all_then strip_assume_tac) >>
       first_x_assum (drule_then strip_assume_tac) >>
       qpat_assum `!a e cid n h b done ent ret. _` (drule_then strip_assume_tac) >>
       `SUC i < LENGTH c1` by simp[] >>
       `FST (EL (SUC i) c1) = (ei,cid)::ai` by metis_tac[] >>
       goal_assum (drule_at Any) >> gvs[])
  >> `i = LENGTH pre` by
       (`i <= LENGTH pre` by
          (gvs[LESS_EQ_IFF_LESS_SUC]) >>
        decide_tac) >>
  `i < LENGTH c0 /\ EL i c0 = (p,D,d,0,z0)` by simp[EL_APPEND_EQN] >>
  qpat_assum `!i ai ds ei qi zi. _ ==> ?sf tf inc entry order res nrest later. _`
    (drule_all_then strip_assume_tac) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Finalise pseudo_current_cut_array

Theorem pseudo_current_cut_flat_length[local]:
  !q (xs:'a list list) (ys:'b list list).
    LIST_REL (\x y. LENGTH x = LENGTH y) xs ys ==>
    LENGTH (FLAT (TAKE q xs)) = LENGTH (FLAT (TAKE q ys))
Proof
  Induct_on `q` >> simp[] >>
  Cases_on `xs` >> Cases_on `ys` >> simp[] >> strip_tac >>
  first_x_assum (drule_then SUBST1_TAC) >> decide_tac
QED

Theorem pseudo_current_cut_before_last[local]:
  ALL_DISTINCT (ds ++ e::later) /\ MEM f ds ==>
  f <> LAST (ds ++ e::later)
Proof
  simp[ALL_DISTINCT_APPEND] >> strip_tac >>
  `MEM (LAST (e::later)) (e::later)` by simp[LAST_MEM] >>
  fs[] >> metis_tac[]
QED

(* The new masks, sites and keys are flattened at the same retained cut.
   In particular, each root prefix below is identified by the literal cut,
   not by choosing a decomposition of the updated root aggregate. *)
Theorem dft_packet_pseudo_current_cut_arrays:
  !(acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (calls : (gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab : (((num # num) list # num), bytes32 option list list) fmap) ms_tab'
    (es_tab : (((num # num) list # num), (string # num) list list) fmap) es_tab'
    (ks_tab : (((num # num) list # num), gas_event list list) fmap) ks_tab'
    pre p D d q z0 z1 c0 c1 cm ce ck AM' AE' AK' M0 E0 K0 M1 E1 K1.
    c0 = pre ++ [(p,D,d,0,z0)] /\ c1 = pre ++ [(p,D,d,q,z1)] /\
    FST (HD c0) = [] /\
    (!i ai ds ei qi (zi:instruction list).
      i < LENGTH c0 /\ EL i c0 = (ai,ds,ei,qi,zi) ==>
      ?sf tf inc entry order res nrest later.
        FLOOKUP acts ai = SOME (sf,tf,inc,entry,order,res,nrest) /\
        order = ds ++ ei::later /\
        (SUC i < LENGTH c0 ==>
          ?cid h b done ent ret.
            FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b,done,ent,ret) /\
            FST (EL (SUC i) c0) = (ei,cid)::ai)) /\
    (!a sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      ALL_DISTINCT order /\ (a = p ==> LAST order = d) /\
      (!i. i < LENGTH p /\ a = DROP (SUC i) p ==> LAST order = FST (EL i p))) /\
    (!a e. (a,e) <> (p,d) /\
      (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
      FLOOKUP ms_tab' (a,e) = FLOOKUP ms_tab (a,e) /\
      FLOOKUP es_tab' (a,e) = FLOOKUP es_tab (a,e) /\
      FLOOKUP ks_tab' (a,e) = FLOOKUP ks_tab (a,e)) /\
    (!a e cid n h b done ent ret.
      FLOOKUP calls (a,e,cid) = SOME (n,h,b,done,ent,ret) ==>
      (TAKE n (THE (FLOOKUP ms_tab' (a,e))) = TAKE n (THE (FLOOKUP ms_tab (a,e))) /\
       ?r. FLOOKUP ms_tab' (a,e) = SOME r /\ n < LENGTH r /\ EL n r = AM' ((e,cid)::a)) /\
      (TAKE n (THE (FLOOKUP es_tab' (a,e))) = TAKE n (THE (FLOOKUP es_tab (a,e))) /\
       ?r. FLOOKUP es_tab' (a,e) = SOME r /\ n < LENGTH r /\ EL n r = AE' ((e,cid)::a)) /\
      (TAKE n (THE (FLOOKUP ks_tab' (a,e))) = TAKE n (THE (FLOOKUP ks_tab (a,e))) /\
       ?r. FLOOKUP ks_tab' (a,e) = SOME r /\ n < LENGTH r /\ EL n r = AK' ((e,cid)::a))) /\
    FLOOKUP ms_tab' (p,d) = SOME cm /\
    FLOOKUP es_tab' (p,d) = SOME ce /\
    FLOOKUP ks_tab' (p,d) = SOME ck /\ q <= LENGTH cm /\
    LIST_REL (\m e. LENGTH m = LENGTH e) cm ce /\
    LIST_REL (\m k. LENGTH m = LENGTH k) cm ck /\
    AM' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab' (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AE' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab' (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    AK' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab' (a,e))))
      (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
    M0 = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) c0) /\
    E0 = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) c0) /\
    K0 = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) c0) /\
    M1 = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei))))) c1) /\
    E1 = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei))))) c1) /\
    K1 = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei))))) c1) /\
    LENGTH M0 = LENGTH E0 /\ LENGTH M0 = LENGTH K0 ==>
    (M1 = M0 ++ FLAT (TAKE q cm) /\ (?mr. AM' [] = M1 ++ mr)) /\
    (E1 = E0 ++ FLAT (TAKE q ce) /\ (?er. AE' [] = E1 ++ er)) /\
    (K1 = K0 ++ FLAT (TAKE q ck) /\ (?kr. AK' [] = K1 ++ kr)) /\
    LENGTH M1 = LENGTH E1 /\ LENGTH M1 = LENGTH K1
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i ai ds ei qi zi f.
      i < LENGTH c0 /\ EL i c0 = (ai,ds,ei,qi,zi) /\ MEM f ds ==>
      FLOOKUP ms_tab' (ai,f) = FLOOKUP ms_tab (ai,f) /\
      FLOOKUP es_tab' (ai,f) = FLOOKUP es_tab (ai,f) /\
      FLOOKUP ks_tab' (ai,f) = FLOOKUP ks_tab (ai,f)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i ai ds ei qi zi. _` (drule_all_then strip_assume_tac) >>
     qpat_assum `!a sf tf inc entry order res nrest. _` (drule_then strip_assume_tac) >>
     `f <> LAST order` by
       (qpat_assum `order = _` SUBST_ALL_TAC >> irule pseudo_current_cut_before_last >>
        asm_rewrite_tac[]) >>
     qpat_assum `!a e. _` (qspecl_then [`ai`,`f`] irule) >>
     simp[pairTheory.PAIR_EQ] >> metis_tac[]) >>
  `LENGTH cm = LENGTH ce /\ LENGTH cm = LENGTH ck` by metis_tac[LIST_REL_LENGTH] >>
  `LENGTH (FLAT (TAKE q cm)) = LENGTH (FLAT (TAKE q ce)) /\
   LENGTH (FLAT (TAKE q cm)) = LENGTH (FLAT (TAKE q ck))` by
    (conj_tac >> irule pseudo_current_cut_flat_length >> first_assum ACCEPT_TAC) >>
  conj_asm1_tac >- suspend "masks" >>
  conj_asm1_tac >- suspend "sites" >>
  conj_asm1_tac >- suspend "keys" >>
  qpat_assum `M1 = M0 ++ _ /\ _` (SUBST1_TAC o CONJUNCT1) >>
  qpat_assum `E1 = E0 ++ _ /\ _` (SUBST1_TAC o CONJUNCT1) >>
  qpat_assum `K1 = K0 ++ _ /\ _` (SUBST1_TAC o CONJUNCT1) >>
  pure_rewrite_tac[LENGTH_APPEND] >>
  qpat_assum `LENGTH M0 = LENGTH E0` (SUBST1_TAC o SYM) >>
  qpat_assum `LENGTH M0 = LENGTH K0` (SUBST1_TAC o SYM) >>
  qpat_assum `LENGTH (FLAT (TAKE q cm)) = LENGTH (FLAT (TAKE q ce))`
    (SUBST1_TAC o SYM) >>
  qpat_assum `LENGTH (FLAT (TAKE q cm)) = LENGTH (FLAT (TAKE q ck))`
    (SUBST1_TAC o SYM) >> simp[]
QED

Resume dft_packet_pseudo_current_cut_arrays[masks]:
  qspecl_then [`acts`,`calls`,`ms_tab`,`ms_tab'`,`AM'`] irule pseudo_current_cut_array >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`D`,`acts`,`c0`,`c1`,`calls`,`d`,`ms_tab`,`ms_tab'`,`p`,`pre`,`z0`,`z1`] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!a e cid n h b done ent ret. _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!i ai ds ei qi zi f. _` (drule_all_then strip_assume_tac) >>
      first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_pseudo_current_cut_arrays[sites]:
  qspecl_then [`acts`,`calls`,`es_tab`,`es_tab'`,`AE'`] irule pseudo_current_cut_array >>
  conj_tac >- metis_tac[] >>
  qexistsl [`D`,`acts`,`c0`,`c1`,`calls`,`d`,`es_tab`,`es_tab'`,`p`,`pre`,`z0`,`z1`] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!a e cid n h b done ent ret. _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!i ai ds ei qi zi f. _` (drule_all_then strip_assume_tac) >>
      first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_pseudo_current_cut_arrays[keys]:
  qspecl_then [`acts`,`calls`,`ks_tab`,`ks_tab'`,`AK'`] irule pseudo_current_cut_array >>
  conj_tac >- metis_tac[] >>
  qexistsl [`D`,`acts`,`c0`,`c1`,`calls`,`d`,`ks_tab`,`ks_tab'`,`p`,`pre`,`z0`,`z1`] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!a e cid n h b done ent ret. _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!i ai ds ei qi zi f. _` (drule_all_then strip_assume_tac) >>
      first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise dft_packet_pseudo_current_cut_arrays
