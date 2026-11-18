Theory dftPacketBlockPathInsertion
Ancestors option[qualified,ignore_grammar]
  dftPacketExistingPathInsertion list rich_list finite_map arithmetic pred_set

Theorem block_flat_length[local]:
  !xs ys. LIST_REL (\x y. LENGTH x = LENGTH y) xs ys ==>
    LENGTH (FLAT xs) = LENGTH (FLAT ys)
Proof
  Induct >- simp[] >> gen_tac >> Cases_on `ys` >> simp[] >>
  metis_tac [ADD_SYM]
QED

Theorem block_aggregate_length[local]:
  !ds a (m:('a # num,'m list list) fmap) (es:('a # num,'e list list) fmap).
  (!f. MEM f ds ==> ?ms ss.
    FLOOKUP m (a,f) = SOME ms /\ FLOOKUP es (a,f) = SOME ss /\
    LIST_REL (\x y. LENGTH x = LENGTH y) ms ss) ==>
  LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP m (a,f)))) ds)) =
  LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP es (a,f)))) ds))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `?ms ss. FLOOKUP m (a,h) = SOME ms /\ FLOOKUP es (a,h) = SOME ss /\
    LIST_REL (\x y. LENGTH x = LENGTH y) ms ss` by metis_tac[] >>
  drule block_flat_length >> strip_tac >> simp[] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem block_sequence_alignment[local]:
  !p:((num # num) list). !inds orders seed cm ce
    (m:(((num # num) list # num),'m list list) fmap)
    (es:(((num # num) list # num),'e list list) fmap) mts ets.
  FDOM m = FDOM es /\
  (!key ms ss. FLOOKUP m key = SOME ms /\ FLOOKUP es key = SOME ss ==>
    LIST_REL (\x y. LENGTH x = LENGTH y) ms ss) /\
  LIST_REL (\x y. LENGTH x = LENGTH y) cm ce /\
  (!i. i < LENGTH p ==> (DROP (SUC i) p,FST (EL i p)) IN FDOM m) /\
  (!i f. i < LENGTH p /\ MEM f (EL i orders) ==>
    (DROP i p,f) IN FDOM m UNION {(p,seed)}) /\
  EL 0 mts = m |+ ((p,seed),cm) /\ EL 0 ets = es |+ ((p,seed),ce) /\
  (!i. i < LENGTH p ==>
    EL (SUC i) mts = EL i mts |+
      ((DROP (SUC i) p,FST (EL i p)),
        LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i mts) (DROP i p,f))))
          (EL i orders))) (EL i inds)
          (THE (FLOOKUP (EL i mts) (DROP (SUC i) p,FST (EL i p)))))) /\
  (!i. i < LENGTH p ==>
    EL (SUC i) ets = EL i ets |+
      ((DROP (SUC i) p,FST (EL i p)),
        LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i ets) (DROP i p,f))))
          (EL i orders))) (EL i inds)
          (THE (FLOOKUP (EL i ets) (DROP (SUC i) p,FST (EL i p)))))) ==>
  !i. i <= LENGTH p ==>
    FDOM (EL i mts) = FDOM m UNION {(p,seed)} /\
    FDOM (EL i ets) = FDOM m UNION {(p,seed)} /\
    (!key ms ss. FLOOKUP (EL i mts) key = SOME ms /\
      FLOOKUP (EL i ets) key = SOME ss ==>
      LIST_REL (\x y. LENGTH x = LENGTH y) ms ss)
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- (simp[FLOOKUP_UPDATE,EXTENSION] >> rpt strip_tac >>
      Cases_on `key = (p,seed)` >> gvs[] >> metis_tac[]) >>
  strip_tac >> `i < LENGTH p /\ i <= LENGTH p` by decide_tac >>
  first_x_assum drule >> strip_tac >>
  `?ms ss. FLOOKUP (EL i mts) (DROP (SUC i) p,FST (EL i p)) = SOME ms /\
    FLOOKUP (EL i ets) (DROP (SUC i) p,FST (EL i p)) = SOME ss /\
    LIST_REL (\x y. LENGTH x = LENGTH y) ms ss` by
    (gvs[flookup_thm] >> metis_tac[]) >>
  `LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i mts) (DROP i p,f))))
      (EL i orders))) =
   LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i ets) (DROP i p,f))))
      (EL i orders)))` by
    (irule block_aggregate_length >> rpt strip_tac >>
     `((DROP i p,f)) IN FDOM m UNION {(p,seed)}` by metis_tac[] >>
     gvs[flookup_thm] >> metis_tac[]) >>
  `EL (SUC i) mts = EL i mts |+
      ((DROP (SUC i) p,FST (EL i p)),
        LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i mts) (DROP i p,f))))
          (EL i orders))) (EL i inds) ms)` by metis_tac[optionTheory.THE_DEF] >>
  `EL (SUC i) ets = EL i ets |+
      ((DROP (SUC i) p,FST (EL i p)),
        LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i ets) (DROP i p,f))))
          (EL i orders))) (EL i inds) ss)` by metis_tac[optionTheory.THE_DEF] >>
  conj_tac >- (simp[EXTENSION] >> metis_tac[]) >>
  conj_tac >- (simp[EXTENSION] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `key = (DROP (SUC i) p,FST (EL i p))`
  >- (gvs[FLOOKUP_UPDATE] >>
      simp[LIST_REL_EL_EQN,EL_LUPDATE] >> rpt strip_tac >>
      Cases_on `n = EL i inds` >> gvs[LIST_REL_EL_EQN]) >>
  gvs[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem block_empty_bridge[local]:
  !p:((num # num) list). !i seed orders oldorder
    (tab:(((num # num) list # num),'v list list) fmap).
  i <= LENGTH p /\ EL 0 orders = oldorder ++ [seed] /\
  ~MEM seed oldorder ==>
  FLAT (MAP (\f. FLAT (THE (FLOOKUP (tab |+ ((p,seed),[])) (DROP i p,f))))
    (EL i orders)) =
  FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (DROP i p,f))))
    (if i = 0 then oldorder else EL i orders))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `i = 0`
  >- (gvs[MAP_APPEND,FLAT_APPEND,FLOOKUP_UPDATE] >>
      AP_TERM_TAC >> irule MAP_CONG >> simp[] >> metis_tac[]) >>
  `DROP i p <> p` by (strip_tac >>
    `LENGTH (DROP i p) = LENGTH p` by metis_tac[] >> gvs[]) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem dft_packet_block_path_insertion:
  !p:((num # num) list). !inds orders oldorder d cm ce ck
    (m:(((num # num) list # num),'m list list) fmap)
    (es:(((num # num) list # num),'e list list) fmap)
    (ks:(((num # num) list # num),'k list list) fmap)
    mts ets kts m' es' ks' AM AM' AE AE' AK AK'.
  LENGTH inds = LENGTH p /\ LENGTH orders = SUC (LENGTH p) /\
  (!i. i <= LENGTH p ==> ALL_DISTINCT (EL i orders)) /\
  EL 0 orders = oldorder ++ [SUC d] /\
  (p,SUC d) NOTIN FDOM m /\ FDOM m = FDOM es /\ FDOM m = FDOM ks /\
  (!key ms ss kk. FLOOKUP m key = SOME ms /\ FLOOKUP es key = SOME ss /\
    FLOOKUP ks key = SOME kk ==>
    LENGTH ms = LENGTH ss /\ LENGTH ms = LENGTH kk /\
    LIST_REL (\x y. LENGTH x = LENGTH y) ms ss /\
    LIST_REL (\x y. LENGTH x = LENGTH y) ms kk) /\
  (!i f. i <= LENGTH p /\ MEM f (EL i orders) ==>
    (DROP i p,f) IN FDOM m UNION {(p,SUC d)}) /\
  (!i. i < LENGTH p ==>
    MEM (FST (EL i p)) (EL (SUC i) orders) /\
    ?mr er kr.
      FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
      FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME er /\
      FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME kr /\
      EL i inds < LENGTH mr /\ EL i inds < LENGTH er /\ EL i inds < LENGTH kr /\
      EL (EL i inds) mr = AM i /\ EL (EL i inds) er = AE i /\
      EL (EL i inds) kr = AK i) /\
  LENGTH cm = LENGTH ce /\ LENGTH cm = LENGTH ck /\
  LIST_REL (\x y. LENGTH x = LENGTH y) cm ce /\
  LIST_REL (\x y. LENGTH x = LENGTH y) cm ck /\
  AM = (\i. FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP i p,f))))
    (if i = 0 then oldorder else EL i orders))) /\
  AE = (\i. FLAT (MAP (\f. FLAT (THE (FLOOKUP es (DROP i p,f))))
    (if i = 0 then oldorder else EL i orders))) /\
  AK = (\i. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks (DROP i p,f))))
    (if i = 0 then oldorder else EL i orders))) /\
  AM' = (\i. FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (DROP i p,f)))) (EL i orders))) /\
  AE' = (\i. FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (DROP i p,f)))) (EL i orders))) /\
  AK' = (\i. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (DROP i p,f)))) (EL i orders))) /\
  EL 0 mts = m |+ ((p,SUC d),cm) /\ m' = EL (LENGTH p) mts /\
  EL 0 ets = es |+ ((p,SUC d),ce) /\ es' = EL (LENGTH p) ets /\
  EL 0 kts = ks |+ ((p,SUC d),ck) /\ ks' = EL (LENGTH p) kts /\
  (!i. i < LENGTH p ==>
    EL (SUC i) mts = EL i mts |+
      ((DROP (SUC i) p,FST (EL i p)),
        LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i mts) (DROP i p,f))))
          (EL i orders))) (EL i inds)
          (THE (FLOOKUP (EL i mts) (DROP (SUC i) p,FST (EL i p)))))) /\
  (!i. i < LENGTH p ==>
    EL (SUC i) ets = EL i ets |+
      ((DROP (SUC i) p,FST (EL i p)),
        LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i ets) (DROP i p,f))))
          (EL i orders))) (EL i inds)
          (THE (FLOOKUP (EL i ets) (DROP (SUC i) p,FST (EL i p)))))) /\
  (!i. i < LENGTH p ==>
    EL (SUC i) kts = EL i kts |+
      ((DROP (SUC i) p,FST (EL i p)),
        LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i kts) (DROP i p,f))))
          (EL i orders))) (EL i inds)
          (THE (FLOOKUP (EL i kts) (DROP (SUC i) p,FST (EL i p)))))) /\
  FLOOKUP m' (p,SUC d) = SOME cm /\ FLOOKUP es' (p,SUC d) = SOME ce /\
  FLOOKUP ks' (p,SUC d) = SOME ck /\
  (!a e. (a,e) <> (p,SUC d) /\
    (!r. r < LENGTH p ==> (a,e) <> (DROP (SUC r) p,FST (EL r p))) ==>
    FLOOKUP m' (a,e) = FLOOKUP m (a,e) /\
    FLOOKUP es' (a,e) = FLOOKUP es (a,e) /\
    FLOOKUP ks' (a,e) = FLOOKUP ks (a,e)) /\
  (!i mr er kr. i < LENGTH p /\
    FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
    FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME er /\
    FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME kr ==>
    FLOOKUP m' (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AM' i) (EL i inds) mr) /\
    FLOOKUP es' (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AE' i) (EL i inds) er) /\
    FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AK' i) (EL i inds) kr)) ==>
  FDOM m' = FDOM m UNION {(p,SUC d)} /\
  FDOM m' = FDOM es' /\ FDOM m' = FDOM ks' /\
  (!key ms ss kk. FLOOKUP m' key = SOME ms /\ FLOOKUP es' key = SOME ss /\
    FLOOKUP ks' key = SOME kk ==>
    LENGTH ms = LENGTH ss /\ LENGTH ms = LENGTH kk /\
    LIST_REL (\x y. LENGTH x = LENGTH y) ms ss /\
    LIST_REL (\x y. LENGTH x = LENGTH y) ms kk) /\
  (?lm rm le re lk rk.
    AM (LENGTH p) = lm ++ rm /\ AM' (LENGTH p) = lm ++ FLAT cm ++ rm /\
    AE (LENGTH p) = le ++ re /\ AE' (LENGTH p) = le ++ FLAT ce ++ re /\
    AK (LENGTH p) = lk ++ rk /\ AK' (LENGTH p) = lk ++ FLAT ck ++ rk /\
    LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
    LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk)
Proof
  rpt gen_tac >> strip_tac >>
  `(!key ms ss. FLOOKUP m key = SOME ms /\ FLOOKUP es key = SOME ss ==>
     LIST_REL (\x y. LENGTH x = LENGTH y) ms ss) /\
   (!key ms kk. FLOOKUP m key = SOME ms /\ FLOOKUP ks key = SOME kk ==>
     LIST_REL (\x y. LENGTH x = LENGTH y) ms kk)` by
    (rpt strip_tac >> gvs[flookup_thm] >> metis_tac[]) >>
  `(!i. i < LENGTH p ==> (DROP (SUC i) p,FST (EL i p)) IN FDOM m) /\
   (!i f. i < LENGTH p /\ MEM f (EL i orders) ==>
     (DROP i p,f) IN FDOM m UNION {(p,SUC d)})` by
    (conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!j. j < LENGTH p ==> MEM _ _ /\ _`
           (qspec_then `i` mp_tac) >> simp[] >>
         gvs[flookup_thm]) >>
     rpt strip_tac >> `i <= LENGTH p` by decide_tac >>
     qpat_assum `!j f. j <= LENGTH p /\ _ ==> _`
       (qspecl_then [`i`,`f`] mp_tac) >> simp[]) >>
  `!i. i <= LENGTH p ==>
    FDOM (EL i mts) = FDOM m UNION {(p,SUC d)} /\
    FDOM (EL i ets) = FDOM m UNION {(p,SUC d)} /\
    (!key ms ss. FLOOKUP (EL i mts) key = SOME ms /\ FLOOKUP (EL i ets) key = SOME ss ==>
      LIST_REL (\x y. LENGTH x = LENGTH y) ms ss)` by
    (ho_match_mp_tac block_sequence_alignment >>
     qexistsl [`inds`,`orders`,`cm`,`ce`,`es`] >> asm_rewrite_tac[] >>
     gvs[block_sequence_alignment]) >>
  `!i. i <= LENGTH p ==>
    FDOM (EL i mts) = FDOM m UNION {(p,SUC d)} /\
    FDOM (EL i kts) = FDOM m UNION {(p,SUC d)} /\
    (!key ms kk. FLOOKUP (EL i mts) key = SOME ms /\ FLOOKUP (EL i kts) key = SOME kk ==>
      LIST_REL (\x y. LENGTH x = LENGTH y) ms kk)` by
    (ho_match_mp_tac block_sequence_alignment >>
     qexistsl [`inds`,`orders`,`cm`,`ck`,`ks`] >> asm_rewrite_tac[]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!i. i <= LENGTH p ==> FDOM (EL i mts) = _ /\ FDOM (EL i ets) = _ /\ _`
        (qspec_then `LENGTH p` mp_tac) >> simp[] >> strip_tac >>
      qpat_assum `!i. i <= LENGTH p ==> FDOM (EL i mts) = _ /\ FDOM (EL i kts) = _ /\ _`
        (qspec_then `LENGTH p` mp_tac) >> simp[] >> strip_tac >>
      gvs[] >>
      qpat_assum `!key ms ss. FLOOKUP (EL (LENGTH p) mts) key = SOME ms /\
        FLOOKUP (EL (LENGTH p) ets) key = SOME ss ==> _`
        (qspecl_then [`key`,`ms`,`ss`] mp_tac) >> simp[] >> strip_tac >>
      qpat_assum `!key ms kk. FLOOKUP (EL (LENGTH p) mts) key = SOME ms /\
        FLOOKUP (EL (LENGTH p) kts) key = SOME kk ==> _`
        (qspecl_then [`key`,`ms`,`kk`] mp_tac) >> simp[] >> strip_tac >>
      gvs[LIST_REL_EL_EQN]) >>
  suspend "insertion"
QED

Resume dft_packet_block_path_insertion[insertion]:
  `~MEM (SUC d) oldorder` by
    (qpat_x_assum `!i. i <= LENGTH p ==> ALL_DISTINCT _`
      (qspec_then `0` mp_tac) >> simp[ALL_DISTINCT_APPEND]) >>
  qabbrev_tac `mb = m |+ ((p,SUC d),[])` >>
  qabbrev_tac `eb = es |+ ((p,SUC d),[])` >>
  qabbrev_tac `kb = ks |+ ((p,SUC d),[])` >>
  `(!i. i <= LENGTH p ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP mb (DROP i p,f)))) (EL i orders)) = AM i) /\
   (!i. i <= LENGTH p ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP eb (DROP i p,f)))) (EL i orders)) = AE i) /\
   (!i. i <= LENGTH p ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP kb (DROP i p,f)))) (EL i orders)) = AK i)` by
    (simp[Abbr `mb`,Abbr `eb`,Abbr `kb`] >>
     rpt strip_tac >> irule block_empty_bridge >> simp[]) >>
  qabbrev_tac `AMb = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP mb (DROP i p,f)))) (EL i orders))` >>
  qabbrev_tac `AEb = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP eb (DROP i p,f)))) (EL i orders))` >>
  qabbrev_tac `AKb = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP kb (DROP i p,f)))) (EL i orders))` >>
  `!i. i <= LENGTH p ==> AMb i = AM i /\ AEb i = AE i /\ AKb i = AK i` by
    simp[Abbr `AMb`,Abbr `AEb`,Abbr `AKb`] >>
  first_assum (qspec_then `LENGTH p` (fn th =>
    pure_once_rewrite_tac [GSYM (SIMP_RULE (srw_ss()) [] th)])) >>
  irule dft_packet_existing_path_triple_insertion >>
  conj_tac >- (irule block_flat_length >> simp[]) >>
  conj_tac >- (irule block_flat_length >> simp[]) >>
  qexistsl [`SUC d`,`oldorder`,`eb`,`es'`,`inds`,`kb`,`ks'`,`mb`,`m'`,`orders`] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!a e. _ ==> FLOOKUP m' (a,e) = FLOOKUP m (a,e) /\ _`
        (qspecl_then [`a`,`e`] mp_tac) >>
      simp[FLOOKUP_UPDATE,Abbr `mb`,Abbr `eb`,Abbr `kb`]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `(DROP i p,f) = (p,SUC d)`
      >- (qpat_assum `(DROP i p,f) = (p,SUC d)` SUBST1_TAC >>
          qexistsl [`[]`,`[]`,`[]`] >> simp[FLOOKUP_UPDATE,Abbr `mb`,Abbr `eb`,Abbr `kb`]) >>
      `(DROP i p,f) IN FDOM m` by
        ((qpat_assum `!i f. i <= LENGTH p /\ _ ==> _`
          (qspecl_then [`i`,`f`] mp_tac) >> gvs[] >> (metis_tac[]))) >>
      `(p,SUC d) <> (DROP i p,f)` by
        (qpat_assum `(DROP i p,f) <> (p,SUC d)` mp_tac >>
         POP_ASSUM_LIST kall_tac >> metis_tac[]) >>
      `?mr er kr. FLOOKUP m (DROP i p,f) = SOME mr /\
        FLOOKUP es (DROP i p,f) = SOME er /\ FLOOKUP ks (DROP i p,f) = SOME kr` by
        (qexistsl [`m ' (DROP i p,f)`,`es ' (DROP i p,f)`,`ks ' (DROP i p,f)`] >>
         gvs[flookup_thm]) >>
      qexistsl [`mr`,`er`,`kr`] >>
      qpat_assum `!key ms ss kk. FLOOKUP m key = SOME ms /\ _ ==> _`
        (qspecl_then [`(DROP i p,f)`,`mr`,`er`,`kr`] mp_tac) >>
      simp[FLOOKUP_UPDATE,Abbr `mb`,Abbr `eb`,Abbr `kb`]) >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_assum `!i. i < LENGTH p ==> MEM _ _ /\ _`
        (qspec_then `i` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
      `DROP (SUC i) p <> p` by
        (strip_tac >> `LENGTH (DROP (SUC i) p) = LENGTH p` by metis_tac[] >> gvs[]) >>
      `i <= LENGTH p` by decide_tac >>
      conj_tac >- simp[] >>
      qexistsl [`mr`,`er`,`kr`] >>
      qpat_assum `!i mr er kr. _ ==> FLOOKUP m' _ = _ /\ _`
        (qspecl_then [`i`,`mr`,`er`,`kr`] mp_tac) >>
      simp[FLOOKUP_UPDATE,Abbr `mb`,Abbr `eb`,Abbr `kb`]) >>
  simp[FLOOKUP_UPDATE,Abbr `AMb`,Abbr `AEb`,Abbr `AKb`] >>
  simp[FLOOKUP_UPDATE,Abbr `mb`,Abbr `eb`,Abbr `kb`]
QED

Finalise dft_packet_block_path_insertion
