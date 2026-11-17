Theory dftPacketCallPathInsertion
Ancestors
  dftPacketCallEdgeClauses list rich_list finite_map arithmetic

Theorem call_flat_lengths[local]:
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

(* Final-map version: only one row of this activation changes. *)
Theorem call_final_row_split[local]:
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

Theorem call_aggregate_lengths[local]:
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
  drule call_flat_lengths >> strip_tac >> simp[] >>
  `LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP m (a,f)))) ds)) =
   LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP s (a,f)))) ds))` by
    (first_x_assum irule >> metis_tac[]) >> simp[]
QED

Theorem call_insertion_chain[local]:
  !L (m:num->'m list) m' (s:num->'s list) s' (k:num->'k list) k' cm ce ck.
    0 < L /\ m' 0 = cm /\ s' 0 = ce /\ k' 0 = ck /\
    (!i. i < L ==> ?lm rm le re lk rk.
      m (SUC i) = lm ++ (if i = 0 then [] else m i) ++ rm /\
      m' (SUC i) = lm ++ m' i ++ rm /\
      s (SUC i) = le ++ (if i = 0 then [] else s i) ++ re /\
      s' (SUC i) = le ++ s' i ++ re /\
      k (SUC i) = lk ++ (if i = 0 then [] else k i) ++ rk /\
      k' (SUC i) = lk ++ k' i ++ rk /\
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
  `!n. 0 < n /\ n <= L ==> ?lm rm le re lk rk.
      m n = lm ++ rm /\ m' n = lm ++ cm ++ rm /\
      s n = le ++ re /\ s' n = le ++ ce ++ re /\
      k n = lk ++ rk /\ k' n = lk ++ ck ++ rk /\
      LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
      LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk` suffices_by
    (disch_then (qspec_then `L` mp_tac) >> simp[]) >>
  Induct >- simp[] >> strip_tac >>
  `n < L` by decide_tac >>
  qpat_x_assum `!i. i < L ==> _` drule >>
  disch_then (qx_choose_then `am` (qx_choose_then `bm`
    (qx_choose_then `ae` (qx_choose_then `be`
    (qx_choose_then `ak` (qx_choose_then `bk` strip_assume_tac)))))) >>
  Cases_on `n = 0`
  >- (qexistsl [`am`,`bm`,`ae`,`be`,`ak`,`bk`] >> gvs[]) >>
  `0 < n /\ n <= L` by decide_tac >>
  first_x_assum drule_all >>
  disch_then (qx_choose_then `lm` (qx_choose_then `rm`
    (qx_choose_then `le` (qx_choose_then `re`
    (qx_choose_then `lk` (qx_choose_then `rk` strip_assume_tac)))))) >>
  qexistsl [`am ++ lm`,`rm ++ bm`,`ae ++ le`,`re ++ be`,`ak ++ lk`,`rk ++ bk`] >>
  simp[APPEND_ASSOC]
QED

Theorem call_path_frame[local]:
  !b:((num # num) list). !seed i f
    (tab:(((num # num) list # num),'v list list) fmap) out.
    i < LENGTH b /\ f <> FST (EL i b) /\
    (!a e. (a,e) <> (b,seed) /\
      (!r. r < LENGTH b ==> (a,e) <> (DROP (SUC r) b,FST (EL r b))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) ==>
    FLOOKUP out (DROP (SUC i) b,f) = FLOOKUP tab (DROP (SUC i) b,f)
Proof
  rpt gen_tac >> strip_tac >> first_x_assum irule >>
  reverse conj_tac
  >- (strip_tac >>
      `LENGTH (DROP (SUC i) b) = LENGTH b` by metis_tac[pairTheory.PAIR_EQ] >>
      gvs[]) >>
  rpt strip_tac >>
  `LENGTH (DROP (SUC i) b) = LENGTH (DROP (SUC r) b)` by
    metis_tac[pairTheory.PAIR_EQ] >>
  `i = r` by (gvs[] >> decide_tac) >> gvs[]
QED

Theorem call_path_row_split[local]:
  !b:((num # num) list). !seed i inds orders ds later rows
    (tab:(((num # num) list # num),'v list list) fmap) out.
    i < LENGTH b /\
    EL (SUC i) orders = ds ++ FST (EL i b)::later /\
    ALL_DISTINCT (EL (SUC i) orders) /\
    FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rows /\
    EL i inds < LENGTH rows /\
    FLOOKUP out (DROP (SUC i) b,FST (EL i b)) =
      SOME (LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP out (DROP i b,f))))
        (EL i orders))) (EL i inds) rows) /\
    (!a e. (a,e) <> (b,seed) /\
      (!r. r < LENGTH b ==> (a,e) <> (DROP (SUC r) b,FST (EL r b))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (DROP (SUC i) b,f))))
      (EL (SUC i) orders)) =
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (DROP (SUC i) b,f)))) ds) ++
        FLAT (TAKE (EL i inds) rows)) ++ EL (EL i inds) rows ++
      (FLAT (DROP (SUC (EL i inds)) rows) ++
        FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (DROP (SUC i) b,f)))) later)) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP out (DROP (SUC i) b,f))))
      (EL (SUC i) orders)) =
      (FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (DROP (SUC i) b,f)))) ds) ++
        FLAT (TAKE (EL i inds) rows)) ++
      FLAT (MAP (\f. FLAT (THE (FLOOKUP out (DROP i b,f)))) (EL i orders)) ++
      (FLAT (DROP (SUC (EL i inds)) rows) ++
        FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (DROP (SUC i) b,f)))) later))
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM (FST (EL i b)) ds /\ ~MEM (FST (EL i b)) later` by
    gvs[ALL_DISTINCT_APPEND] >>
  qpat_x_assum `EL (SUC i) orders = _` SUBST1_TAC >>
  irule call_final_row_split >> simp[] >>
  rpt strip_tac >> irule call_path_frame >> simp[] >>
  (reverse conj_tac >- metis_tac[] >>
   qexists_tac `seed` >> metis_tac[pairTheory.PAIR_EQ])
QED

Theorem dft_packet_call_path_insertion:
  !b:((num # num) list). !inds orders seed
    (m:(((num # num) list # num),bytes32 option list list) fmap) m'
    (s:(((num # num) list # num),(string # num) list list) fmap) s'
    (k:(((num # num) list # num),gas_event list list) fmap) k' cm ce ck.
    b <> [] /\ LENGTH inds = LENGTH b /\ LENGTH orders = SUC (LENGTH b) /\
    EL 0 orders = [seed] /\
    FLOOKUP m' (b,seed) = SOME cm /\ FLOOKUP s' (b,seed) = SOME ce /\
    FLOOKUP k' (b,seed) = SOME ck /\
    LENGTH (FLAT cm) = LENGTH (FLAT ce) /\ LENGTH (FLAT cm) = LENGTH (FLAT ck) /\
    (!a e. (a,e) <> (b,seed) /\
      (!r. r < LENGTH b ==> (a,e) <> (DROP (SUC r) b,FST (EL r b))) ==>
      FLOOKUP m' (a,e) = FLOOKUP m (a,e) /\
      FLOOKUP s' (a,e) = FLOOKUP s (a,e) /\
      FLOOKUP k' (a,e) = FLOOKUP k (a,e)) /\
    (!i. i < LENGTH b ==>
      ALL_DISTINCT (EL (SUC i) orders) /\
      MEM (FST (EL i b)) (EL (SUC i) orders) /\
      ?ms ss ks.
        FLOOKUP m (DROP (SUC i) b,FST (EL i b)) = SOME ms /\
        FLOOKUP s (DROP (SUC i) b,FST (EL i b)) = SOME ss /\
        FLOOKUP k (DROP (SUC i) b,FST (EL i b)) = SOME ks /\
        EL i inds < LENGTH ms /\ EL i inds < LENGTH ss /\ EL i inds < LENGTH ks /\
        EL (EL i inds) ms = (if i = 0 then [] else
          FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP i b,f)))) (EL i orders))) /\
        EL (EL i inds) ss = (if i = 0 then [] else
          FLAT (MAP (\f. FLAT (THE (FLOOKUP s (DROP i b,f)))) (EL i orders))) /\
        EL (EL i inds) ks = (if i = 0 then [] else
          FLAT (MAP (\f. FLAT (THE (FLOOKUP k (DROP i b,f)))) (EL i orders))) /\
        FLOOKUP m' (DROP (SUC i) b,FST (EL i b)) =
          SOME (LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (DROP i b,f))))
            (EL i orders))) (EL i inds) ms) /\
        FLOOKUP s' (DROP (SUC i) b,FST (EL i b)) =
          SOME (LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP s' (DROP i b,f))))
            (EL i orders))) (EL i inds) ss) /\
        FLOOKUP k' (DROP (SUC i) b,FST (EL i b)) =
          SOME (LUPDATE (FLAT (MAP (\f. FLAT (THE (FLOOKUP k' (DROP i b,f))))
            (EL i orders))) (EL i inds) ks)) /\
    (!i f. i < LENGTH b /\ MEM f (EL (SUC i) orders) ==>
      ?ms ss ks. FLOOKUP m (DROP (SUC i) b,f) = SOME ms /\
        FLOOKUP s (DROP (SUC i) b,f) = SOME ss /\
        FLOOKUP k (DROP (SUC i) b,f) = SOME ks /\
        LENGTH ms = LENGTH ss /\ LENGTH ms = LENGTH ks /\
        LIST_REL (\x y. LENGTH x = LENGTH y) ms ss /\
        LIST_REL (\x y. LENGTH x = LENGTH y) ms ks) ==>
    ?lm rm le re lk rk.
      FLAT (MAP (\f. FLAT (THE (FLOOKUP m ([],f)))) (EL (LENGTH b) orders)) = lm ++ rm /\
      FLAT (MAP (\f. FLAT (THE (FLOOKUP m' ([],f)))) (EL (LENGTH b) orders)) = lm ++ FLAT cm ++ rm /\
      FLAT (MAP (\f. FLAT (THE (FLOOKUP s ([],f)))) (EL (LENGTH b) orders)) = le ++ re /\
      FLAT (MAP (\f. FLAT (THE (FLOOKUP s' ([],f)))) (EL (LENGTH b) orders)) = le ++ FLAT ce ++ re /\
      FLAT (MAP (\f. FLAT (THE (FLOOKUP k ([],f)))) (EL (LENGTH b) orders)) = lk ++ rk /\
      FLAT (MAP (\f. FLAT (THE (FLOOKUP k' ([],f)))) (EL (LENGTH b) orders)) = lk ++ FLAT ck ++ rk /\
      LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
      LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `ma = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP i b,f)))) (EL i orders))` >>
  qabbrev_tac `mb = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (DROP i b,f)))) (EL i orders))` >>
  qabbrev_tac `sa = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP s (DROP i b,f)))) (EL i orders))` >>
  qabbrev_tac `sb = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP s' (DROP i b,f)))) (EL i orders))` >>
  qabbrev_tac `ka = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP k (DROP i b,f)))) (EL i orders))` >>
  qabbrev_tac `kb = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP k' (DROP i b,f)))) (EL i orders))` >>
  `!i. i < LENGTH b ==> ?lm rm le re lk rk.
      ma (SUC i) = lm ++ (if i = 0 then [] else ma i) ++ rm /\
      mb (SUC i) = lm ++ mb i ++ rm /\
      sa (SUC i) = le ++ (if i = 0 then [] else sa i) ++ re /\
      sb (SUC i) = le ++ sb i ++ re /\
      ka (SUC i) = lk ++ (if i = 0 then [] else ka i) ++ rk /\
      kb (SUC i) = lk ++ kb i ++ rk /\
      LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
      LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH b ==> _` drule >> strip_tac >>
     `?ds later. EL (SUC i) orders = ds ++ FST (EL i b)::later` by metis_tac[MEM_SPLIT] >>
     qexistsl [
       `FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP (SUC i) b,f)))) ds) ++ FLAT (TAKE (EL i inds) ms)`,
       `FLAT (DROP (SUC (EL i inds)) ms) ++ FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP (SUC i) b,f)))) later)`,
       `FLAT (MAP (\f. FLAT (THE (FLOOKUP s (DROP (SUC i) b,f)))) ds) ++ FLAT (TAKE (EL i inds) ss)`,
       `FLAT (DROP (SUC (EL i inds)) ss) ++ FLAT (MAP (\f. FLAT (THE (FLOOKUP s (DROP (SUC i) b,f)))) later)`,
       `FLAT (MAP (\f. FLAT (THE (FLOOKUP k (DROP (SUC i) b,f)))) ds) ++ FLAT (TAKE (EL i inds) ks)`,
       `FLAT (DROP (SUC (EL i inds)) ks) ++ FLAT (MAP (\f. FLAT (THE (FLOOKUP k (DROP (SUC i) b,f)))) later)`] >>
     conj_tac
     >- (simp[NoAsms,Abbr `ma`] >>
         qpat_assum `EL (EL i inds) ms = _` (fn th => once_rewrite_tac[GSYM th]) >>
         irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 1 call_path_row_split)) >>
         simp[] >> qexistsl [`m'`,`seed`] >> simp[] >> metis_tac[]) >>
     conj_tac
     >- (simp[NoAsms,Abbr `mb`] >>
         irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 2 call_path_row_split)) >>
         simp[] >> qexists_tac `seed` >> metis_tac[pairTheory.PAIR_EQ]) >>
     conj_tac
     >- (simp[NoAsms,Abbr `sa`] >>
         qpat_assum `EL (EL i inds) ss = _` (fn th => once_rewrite_tac[GSYM th]) >>
         irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 1 call_path_row_split)) >>
         metis_tac[]) >>
     conj_tac
     >- (simp[NoAsms,Abbr `sb`] >>
         irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 2 call_path_row_split)) >>
         simp[] >> qexists_tac `seed` >> metis_tac[pairTheory.PAIR_EQ]) >>
     conj_tac
     >- (simp[NoAsms,Abbr `ka`] >>
         qpat_assum `EL (EL i inds) ks = _` (fn th => once_rewrite_tac[GSYM th]) >>
         irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 1 call_path_row_split)) >>
         metis_tac[]) >>
     conj_tac
     >- (simp[NoAsms,Abbr `kb`] >>
         irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 2 call_path_row_split)) >>
         simp[] >> qexists_tac `seed` >> metis_tac[pairTheory.PAIR_EQ]) >>
     `LIST_REL (\x y. LENGTH x = LENGTH y) ms ss /\
      LIST_REL (\x y. LENGTH x = LENGTH y) ms ks` by metis_tac[optionTheory.SOME_11] >>
     imp_res_tac call_flat_lengths >>
     `!fs. (!f. MEM f fs ==> MEM f (EL (SUC i) orders)) ==>
       LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP (SUC i) b,f)))) fs)) =
       LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP s (DROP (SUC i) b,f)))) fs)) /\
       LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP (SUC i) b,f)))) fs)) =
       LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP k (DROP (SUC i) b,f)))) fs))` by
       (gen_tac >> strip_tac >> conj_tac >>
        irule call_aggregate_lengths >> metis_tac[]) >>
     qpat_assum `!fs. _` (qspec_then `ds` mp_tac) >>
     qpat_x_assum `!fs. _` (qspec_then `later` mp_tac) >>
     simp[] >> rpt strip_tac >> metis_tac[]) >>
  `0 < LENGTH b /\ mb 0 = FLAT cm /\ sb 0 = FLAT ce /\ kb 0 = FLAT ck` by
    simp[Abbr `mb`,Abbr `sb`,Abbr `kb`,LENGTH_NON_NIL] >>
  drule_all call_insertion_chain >>
  simp[Abbr `ma`,Abbr `mb`,Abbr `sa`,Abbr `sb`,Abbr `ka`,Abbr `kb`]
QED
