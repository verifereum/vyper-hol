Theory dftPacketExistingPathInsertion
Ancestors
  list rich_list finite_map arithmetic

Theorem insertion_flat_lengths:
  !xs ys. LIST_REL (\x y. LENGTH x = LENGTH y) xs ys ==>
    LENGTH (FLAT xs) = LENGTH (FLAT ys) /\
    (!n. LENGTH (FLAT (TAKE n xs)) = LENGTH (FLAT (TAKE n ys))) /\
    (!n. LENGTH (FLAT (DROP n xs)) = LENGTH (FLAT (DROP n ys)))
Proof
  Induct_on `xs` >- simp[] >> gen_tac >> strip_tac >>
  Cases_on `ys` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac >- simp[] >> conj_tac >> gen_tac >> Cases_on `n` >> simp[]
QED

Theorem insertion_aggregate_lengths:
  !ds a (m:(((num # num) list # num),'m list list) fmap)
    (s:(((num # num) list # num),'s list list) fmap).
    (!f. MEM f ds ==> ?ms ss.
      FLOOKUP m (a,f) = SOME ms /\ FLOOKUP s (a,f) = SOME ss /\
      LIST_REL (\x y. LENGTH x = LENGTH y) ms ss) ==>
    LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP m (a,f)))) ds)) =
    LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP s (a,f)))) ds))
Proof
  Induct_on `ds` >> simp[] >> rpt strip_tac >>
  `?ms ss. FLOOKUP m (a,h) = SOME ms /\ FLOOKUP s (a,h) = SOME ss /\
    LIST_REL (\x y. LENGTH x = LENGTH y) ms ss` by metis_tac[] >>
  drule insertion_flat_lengths >> strip_tac >> simp[] >>
  `LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP m (a,f)))) ds)) =
   LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP s (a,f)))) ds))` by
    (first_x_assum irule >> metis_tac[]) >> simp[]
QED

Theorem insertion_path_frame[local]:
  !p:((num # num) list). !d i f
    (tab:(((num # num) list # num),'v list list) fmap) out.
    i <= LENGTH p /\ (if i = 0 then f <> d else f <> FST (EL (i-1) p)) /\
    (!a e. (a,e) <> (p,d) /\
      (!r. r < LENGTH p ==> (a,e) <> (DROP (SUC r) p,FST (EL r p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) ==>
    FLOOKUP out (DROP i p,f) = FLOOKUP tab (DROP i p,f)
Proof
  rpt gen_tac >> strip_tac >> first_x_assum irule >>
  reverse conj_tac
  >- (strip_tac >>
      `LENGTH (DROP i p) = LENGTH p` by metis_tac[pairTheory.PAIR_EQ] >>
      gvs[] >> Cases_on `i = 0` >> gvs[]) >>
  rpt strip_tac >>
  `LENGTH (DROP i p) = LENGTH (DROP (SUC r) p)` by
    metis_tac[pairTheory.PAIR_EQ] >>
  `i = SUC r` by (gvs[] >> decide_tac) >> gvs[]
QED

Theorem insertion_row_split:
  !a e ds later q rows v
    (tab:(((num # num) list # num),'v list list) fmap) out.
    ~MEM e ds /\ ~MEM e later /\
    FLOOKUP tab (a,e) = SOME rows /\ q < LENGTH rows /\
    FLOOKUP out (a,e) = SOME (LUPDATE v q rows) /\
    (!f. MEM f (ds ++ later) ==> FLOOKUP out (a,f) = FLOOKUP tab (a,f)) ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) (ds ++ e::later)) =
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) ds) ++ FLAT (TAKE q rows)) ++
      EL q rows ++
      (FLAT (DROP (SUC q) rows) ++ FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) later)) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP out (a,f)))) (ds ++ e::later)) =
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) ds) ++ FLAT (TAKE q rows)) ++
      v ++
      (FLAT (DROP (SUC q) rows) ++ FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) later))
Proof
  rpt gen_tac >> strip_tac >>
  `rows = TAKE q rows ++ [EL q rows] ++ DROP (SUC q) rows` by
    metis_tac[TAKE_DROP_SUC] >>
  `LUPDATE v q rows = TAKE q rows ++ [v] ++ DROP (SUC q) rows` by
    (qpat_x_assum `rows = _` (fn th =>
       CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV th)))) >>
     `q = LENGTH (TAKE q rows)` by simp[] >>
     pop_assum (fn th => CONV_TAC (LHS_CONV (RATOR_CONV (RAND_CONV (REWR_CONV th))))) >>
     rewrite_tac[lupdate_append2]) >>
  `MAP (\f. FLAT (THE (FLOOKUP out (a,f)))) ds =
    MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) ds` by
    (irule MAP_CONG >> simp[]) >>
  `MAP (\f. FLAT (THE (FLOOKUP out (a,f)))) later =
    MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) later` by
    (irule MAP_CONG >> simp[]) >>
  conj_tac
  >- (simp[MAP_APPEND,FLAT_APPEND] >>
      qpat_x_assum `rows = _` (fn th =>
        CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV th)))) >>
      simp[FLAT_APPEND,APPEND_ASSOC]) >>
  simp[MAP_APPEND,FLAT_APPEND,APPEND_ASSOC]
QED

Theorem insertion_parent_split[local]:
  !p:((num # num) list). !d i inds orders ds later rows
    (tab:(((num # num) list # num),'v list list) fmap) out.
    i < LENGTH p /\
    EL (SUC i) orders = ds ++ FST (EL i p)::later /\
    ALL_DISTINCT (EL (SUC i) orders) /\
    FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows /\
    EL i inds < LENGTH rows /\
    FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
      SOME (LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP out (DROP i p,f))))
        (EL i orders))) (EL i inds) rows) /\
    (!a e. (a,e) <> (p,d) /\
      (!r. r < LENGTH p ==> (a,e) <> (DROP (SUC r) p,FST (EL r p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (DROP (SUC i) p,f))))
      (EL (SUC i) orders)) =
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (DROP (SUC i) p,f)))) ds) ++
        FLAT (TAKE (EL i inds) rows)) ++ EL (EL i inds) rows ++
      (FLAT (DROP (SUC (EL i inds)) rows) ++
        FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (DROP (SUC i) p,f)))) later)) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP out (DROP (SUC i) p,f))))
      (EL (SUC i) orders)) =
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (DROP (SUC i) p,f)))) ds) ++
        FLAT (TAKE (EL i inds) rows)) ++
      FLAT (MAP (\f. FLAT (THE (FLOOKUP out (DROP i p,f)))) (EL i orders)) ++
      (FLAT (DROP (SUC (EL i inds)) rows) ++
        FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (DROP (SUC i) p,f)))) later))
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM (FST (EL i p)) ds /\ ~MEM (FST (EL i p)) later` by
    gvs[ALL_DISTINCT_APPEND] >>
  qpat_x_assum `EL (SUC i) orders = _` SUBST1_TAC >>
  irule insertion_row_split >> simp[] >>
  rpt strip_tac >> irule insertion_path_frame >> simp[] >>
  qexists_tac `d` >> metis_tac[pairTheory.PAIR_EQ]
QED

Theorem insertion_bottom_split[local]:
  !p:((num # num) list). !d ds orders
    (tab:(((num # num) list # num),'v list list) fmap) out rows.
    ALL_DISTINCT (EL 0 orders) /\ EL 0 orders = ds ++ [d] /\
    FLOOKUP tab (p,d) = SOME [] /\ FLOOKUP out (p,d) = SOME rows /\
    (!a e. (a,e) <> (p,d) /\
      (!r. r < LENGTH p ==> (a,e) <> (DROP (SUC r) p,FST (EL r p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (p,f)))) (EL 0 orders)) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (p,f)))) ds) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP out (p,f)))) (EL 0 orders)) =
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (p,f)))) ds) ++ FLAT rows
Proof
  rpt gen_tac >> strip_tac >>
  `!f. MEM f ds ==> f <> d` by gvs[ALL_DISTINCT_APPEND] >>
  `MAP (\f. FLAT (THE (FLOOKUP out (p,f)))) ds =
   MAP (\f. FLAT (THE (FLOOKUP tab (p,f)))) ds` by
    (irule MAP_CONG >> simp[] >> rpt strip_tac >>
     rename1 `MEM f ds` >>
     `FLOOKUP out (DROP 0 p,f) = FLOOKUP tab (DROP 0 p,f)` by
       (irule insertion_path_frame >> simp[] >> qexists_tac `d` >> simp[]) >>
     gvs[]) >>
  simp[MAP_APPEND,FLAT_APPEND]
QED

Theorem existing_insertion_chain[local]:
  !L (m:num->'m list) m' (s:num->'s list) s' (k:num->'k list) k' cm ce ck.
    (?lm le lk. m 0 = lm /\ m' 0 = lm ++ cm /\
      s 0 = le /\ s' 0 = le ++ ce /\ k 0 = lk /\ k' 0 = lk ++ ck /\
      LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk) /\
    (!i. i < L ==> ?lm rm le re lk rk.
      m (SUC i) = lm ++ m i ++ rm /\ m' (SUC i) = lm ++ m' i ++ rm /\
      s (SUC i) = le ++ s i ++ re /\ s' (SUC i) = le ++ s' i ++ re /\
      k (SUC i) = lk ++ k i ++ rk /\ k' (SUC i) = lk ++ k' i ++ rk /\
      LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
      LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk) ==>
    ?lm rm le re lk rk.
      m L = lm ++ rm /\ m' L = lm ++ cm ++ rm /\
      s L = le ++ re /\ s' L = le ++ ce ++ re /\
      k L = lk ++ rk /\ k' L = lk ++ ck ++ rk /\
      LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
      LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk
Proof
  rpt gen_tac >> strip_tac >>
  `!n. n <= L ==> ?lm rm le re lk rk.
      m n = lm ++ rm /\ m' n = lm ++ cm ++ rm /\
      s n = le ++ re /\ s' n = le ++ ce ++ re /\
      k n = lk ++ rk /\ k' n = lk ++ ck ++ rk /\
      LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
      LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk` suffices_by
    (disch_then (qspec_then `L` mp_tac) >> simp[]) >>
  Induct
  >- (strip_tac >> qexistsl [`lm`,`[]`,`le`,`[]`,`lk`,`[]`] >> simp[]) >>
  strip_tac >> `n < L /\ n <= L` by decide_tac >>
  qpat_x_assum `!i. i < L ==> _` drule >>
  disch_then (qx_choose_then `am` (qx_choose_then `bm`
    (qx_choose_then `ae` (qx_choose_then `be`
    (qx_choose_then `ak` (qx_choose_then `bk` strip_assume_tac)))))) >>
  first_x_assum drule >>
  disch_then (qx_choose_then `lm1` (qx_choose_then `rm1`
    (qx_choose_then `le1` (qx_choose_then `re1`
    (qx_choose_then `lk1` (qx_choose_then `rk1` strip_assume_tac)))))) >>
  qexistsl [`am ++ lm1`,`rm1 ++ bm`,`ae ++ le1`,`re1 ++ be`,`ak ++ lk1`,`rk1 ++ bk`] >>
  simp[APPEND_ASSOC]
QED

Theorem dft_packet_existing_path_triple_insertion:
  !p:((num # num) list). !inds orders ds d
    (m:(((num # num) list # num),'m list list) fmap) m'
    (es:(((num # num) list # num),'e list list) fmap) es'
    (ks:(((num # num) list # num),'k list list) fmap) ks'
    cm ce ck AM AM' AE AE' AK AK'.
    LENGTH inds = LENGTH p /\ LENGTH orders = SUC (LENGTH p) /\
    (!i. i <= LENGTH p ==> ALL_DISTINCT (EL i orders)) /\
    EL 0 orders = ds ++ [d] /\
    AM = (\i. FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP i p,f)))) (EL i orders))) /\
    AM' = (\i. FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (DROP i p,f)))) (EL i orders))) /\
    AE = (\i. FLAT (MAP (\f. FLAT (THE (FLOOKUP es (DROP i p,f)))) (EL i orders))) /\
    AE' = (\i. FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (DROP i p,f)))) (EL i orders))) /\
    AK = (\i. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks (DROP i p,f)))) (EL i orders))) /\
    AK' = (\i. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (DROP i p,f)))) (EL i orders))) /\
    FLOOKUP m (p,d) = SOME [] /\ FLOOKUP es (p,d) = SOME [] /\
    FLOOKUP ks (p,d) = SOME [] /\
    FLOOKUP m' (p,d) = SOME cm /\ FLOOKUP es' (p,d) = SOME ce /\
    FLOOKUP ks' (p,d) = SOME ck /\
    LENGTH (FLAT cm) = LENGTH (FLAT ce) /\ LENGTH (FLAT cm) = LENGTH (FLAT ck) /\
    (!a e. (a,e) <> (p,d) /\
      (!r. r < LENGTH p ==> (a,e) <> (DROP (SUC r) p,FST (EL r p))) ==>
      FLOOKUP m' (a,e) = FLOOKUP m (a,e) /\
      FLOOKUP es' (a,e) = FLOOKUP es (a,e) /\
      FLOOKUP ks' (a,e) = FLOOKUP ks (a,e)) /\
    (!i f. i <= LENGTH p /\ MEM f (EL i orders) ==>
      ?mr er kr. FLOOKUP m (DROP i p,f) = SOME mr /\
        FLOOKUP es (DROP i p,f) = SOME er /\ FLOOKUP ks (DROP i p,f) = SOME kr /\
        LENGTH mr = LENGTH er /\ LENGTH mr = LENGTH kr /\
        LIST_REL (\x y. LENGTH x = LENGTH y) mr er /\
        LIST_REL (\x y. LENGTH x = LENGTH y) mr kr) /\
    (!i. i < LENGTH p ==>
      MEM (FST (EL i p)) (EL (SUC i) orders) /\
      ?mr er kr.
        FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
        FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME er /\
        FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME kr /\
        EL i inds < LENGTH mr /\ EL i inds < LENGTH er /\ EL i inds < LENGTH kr /\
        EL (EL i inds) mr = AM i /\ EL (EL i inds) er = AE i /\
        EL (EL i inds) kr = AK i /\
        FLOOKUP m' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AM' i) (EL i inds) mr) /\
        FLOOKUP es' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AE' i) (EL i inds) er) /\
        FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AK' i) (EL i inds) kr)) ==>
    ?lm rm le re lk rk.
      AM (LENGTH p) = lm ++ rm /\ AM' (LENGTH p) = lm ++ FLAT cm ++ rm /\
      AE (LENGTH p) = le ++ re /\ AE' (LENGTH p) = le ++ FLAT ce ++ re /\
      AK (LENGTH p) = lk ++ rk /\ AK' (LENGTH p) = lk ++ FLAT ck ++ rk /\
      LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
      LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk
Proof
  rpt gen_tac >> strip_tac >>
  irule existing_insertion_chain >> reverse conj_tac
  >- suspend "bottom"
  >> suspend "parents"
QED

Resume dft_packet_existing_path_triple_insertion[bottom]:
  map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
    [`AM = _`,`AM' = _`,`AE = _`,`AE' = _`,`AK = _`,`AK' = _`] >>
  BETA_TAC >>
  qexistsl [
    `FLAT (MAP (\f. FLAT (THE (FLOOKUP m (p,f)))) ds)`,
    `FLAT (MAP (\f. FLAT (THE (FLOOKUP es (p,f)))) ds)`,
    `FLAT (MAP (\f. FLAT (THE (FLOOKUP ks (p,f)))) ds)`] >>
  rpt conj_tac
  >- simp[cj 1 insertion_bottom_split]
  >- (pure_rewrite_tac[DROP_0] >> irule (cj 2 insertion_bottom_split) >>
      conj_tac >- (first_x_assum irule >> simp[]) >>
      qexists_tac `d` >> simp[])
  >- simp[cj 1 insertion_bottom_split]
  >- (pure_rewrite_tac[DROP_0] >> irule (cj 2 insertion_bottom_split) >>
      conj_tac >- (first_x_assum irule >> simp[]) >>
      qexists_tac `d` >> simp[])
  >- simp[cj 1 insertion_bottom_split]
  >- (pure_rewrite_tac[DROP_0] >> irule (cj 2 insertion_bottom_split) >>
      conj_tac >- (first_x_assum irule >> simp[]) >>
      qexists_tac `d` >> simp[])
  >> irule insertion_aggregate_lengths >> rpt strip_tac >>
     qpat_x_assum `!i f. _` (qspecl_then [`0`,`f`] mp_tac) >>
     simp[] >> metis_tac[]
QED

Resume dft_packet_existing_path_triple_insertion[parents]:
  gen_tac >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH p ==> _` drule >> strip_tac >>
  `?pre later. EL (SUC i) orders = pre ++ FST (EL i p)::later` by
    metis_tac[MEM_SPLIT] >>
  qexistsl [
    `FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP (SUC i) p,f)))) pre) ++ FLAT (TAKE (EL i inds) mr)`,
    `FLAT (DROP (SUC (EL i inds)) mr) ++ FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP (SUC i) p,f)))) later)`,
    `FLAT (MAP (\f. FLAT (THE (FLOOKUP es (DROP (SUC i) p,f)))) pre) ++ FLAT (TAKE (EL i inds) er)`,
    `FLAT (DROP (SUC (EL i inds)) er) ++ FLAT (MAP (\f. FLAT (THE (FLOOKUP es (DROP (SUC i) p,f)))) later)`,
    `FLAT (MAP (\f. FLAT (THE (FLOOKUP ks (DROP (SUC i) p,f)))) pre) ++ FLAT (TAKE (EL i inds) kr)`,
    `FLAT (DROP (SUC (EL i inds)) kr) ++ FLAT (MAP (\f. FLAT (THE (FLOOKUP ks (DROP (SUC i) p,f)))) later)`] >>
  conj_tac
  >- (simp[NoAsms] >>
      qpat_assum `EL (EL i inds) mr = _` (fn th => once_rewrite_tac[GSYM th]) >>
      map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
        [`AM = _`,`AM' = _`,`AE = _`,`AE' = _`,`AK = _`,`AK' = _`] >> BETA_TAC >>
      irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 1 insertion_parent_split)) >>
      simp[] >> qexistsl [`d`,`m'`] >> simp[]) >>
  conj_tac
  >- (simp[NoAsms] >>
      map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
        [`AM = _`,`AM' = _`,`AE = _`,`AE' = _`,`AK = _`,`AK' = _`] >> BETA_TAC >>
      irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 2 insertion_parent_split)) >>
      simp[] >> qexists_tac `d` >> metis_tac[pairTheory.PAIR_EQ]) >>
  conj_tac
  >- (simp[NoAsms] >>
      qpat_assum `EL (EL i inds) er = _` (fn th => once_rewrite_tac[GSYM th]) >>
      map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
        [`AM = _`,`AM' = _`,`AE = _`,`AE' = _`,`AK = _`,`AK' = _`] >> BETA_TAC >>
      irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 1 insertion_parent_split)) >>
      simp[] >> qexistsl [`d`,`es'`] >> simp[]) >>
  conj_tac
  >- (simp[NoAsms] >>
      map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
        [`AM = _`,`AM' = _`,`AE = _`,`AE' = _`,`AK = _`,`AK' = _`] >> BETA_TAC >>
      irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 2 insertion_parent_split)) >>
      simp[] >> qexists_tac `d` >> metis_tac[pairTheory.PAIR_EQ]) >>
  conj_tac
  >- (simp[NoAsms] >>
      qpat_assum `EL (EL i inds) kr = _` (fn th => once_rewrite_tac[GSYM th]) >>
      map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
        [`AM = _`,`AM' = _`,`AE = _`,`AE' = _`,`AK = _`,`AK' = _`] >> BETA_TAC >>
      irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 1 insertion_parent_split)) >>
      simp[] >> qexistsl [`d`,`ks'`] >> simp[]) >>
  conj_tac
  >- (simp[NoAsms] >>
      map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
        [`AM = _`,`AM' = _`,`AE = _`,`AE' = _`,`AK = _`,`AK' = _`] >> BETA_TAC >>
      irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 2 insertion_parent_split)) >>
      simp[] >> qexists_tac `d` >> metis_tac[pairTheory.PAIR_EQ]) >>
  `LIST_REL (\x y. LENGTH x = LENGTH y) mr er /\
   LIST_REL (\x y. LENGTH x = LENGTH y) mr kr` by
    (qpat_x_assum `!i f. _`
       (qspecl_then [`SUC i`,`FST (EL i p)`] mp_tac) >>
     simp[] >> metis_tac[optionTheory.SOME_11]) >>
  imp_res_tac insertion_flat_lengths >>
  `!fs. (!f. MEM f fs ==> MEM f (EL (SUC i) orders)) ==>
    LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP (SUC i) p,f)))) fs)) =
    LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP es (DROP (SUC i) p,f)))) fs)) /\
    LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP (SUC i) p,f)))) fs)) =
    LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP ks (DROP (SUC i) p,f)))) fs))` by
    (gen_tac >> strip_tac >> conj_tac >> irule insertion_aggregate_lengths >>
     rpt strip_tac >> qpat_x_assum `!i f. _` (qspecl_then [`SUC i`,`f`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  qpat_assum `!fs. _` (qspec_then `pre` mp_tac) >>
  qpat_x_assum `!fs. _` (qspec_then `later` mp_tac) >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Finalise dft_packet_existing_path_triple_insertion
