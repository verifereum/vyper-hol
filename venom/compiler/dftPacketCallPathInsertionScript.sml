Theory dftPacketCallPathInsertion
Ancestors
  dftPacketExistingPathInsertion
  dftPacketCallEdgeClauses list rich_list finite_map arithmetic

(* Final-map version: only one row of this activation changes. *)
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

Theorem dft_packet_call_path_insertion_at_level:
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
    !n. 0 < n /\ n <= LENGTH b ==> ?lm rm le re lk rk.
      FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP n b,f)))) (EL n orders)) = lm ++ rm /\
      FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (DROP n b,f)))) (EL n orders)) = lm ++ FLAT cm ++ rm /\
      FLAT (MAP (\f. FLAT (THE (FLOOKUP s (DROP n b,f)))) (EL n orders)) = le ++ re /\
      FLAT (MAP (\f. FLAT (THE (FLOOKUP s' (DROP n b,f)))) (EL n orders)) = le ++ FLAT ce ++ re /\
      FLAT (MAP (\f. FLAT (THE (FLOOKUP k (DROP n b,f)))) (EL n orders)) = lk ++ rk /\
      FLAT (MAP (\f. FLAT (THE (FLOOKUP k' (DROP n b,f)))) (EL n orders)) = lk ++ FLAT ck ++ rk /\
      LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
      LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  qabbrev_tac `ma = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP i b,f)))) (EL i orders))` >>
  qabbrev_tac `mb = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (DROP i b,f)))) (EL i orders))` >>
  qabbrev_tac `sa = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP s (DROP i b,f)))) (EL i orders))` >>
  qabbrev_tac `sb = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP s' (DROP i b,f)))) (EL i orders))` >>
  qabbrev_tac `ka = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP k (DROP i b,f)))) (EL i orders))` >>
  qabbrev_tac `kb = \i. FLAT (MAP (\f. FLAT (THE (FLOOKUP k' (DROP i b,f)))) (EL i orders))` >>
  `!i. i < n ==> ?lm rm le re lk rk.
      ma (SUC i) = lm ++ (if i = 0 then [] else ma i) ++ rm /\
      mb (SUC i) = lm ++ mb i ++ rm /\
      sa (SUC i) = le ++ (if i = 0 then [] else sa i) ++ re /\
      sb (SUC i) = le ++ sb i ++ re /\
      ka (SUC i) = lk ++ (if i = 0 then [] else ka i) ++ rk /\
      kb (SUC i) = lk ++ kb i ++ rk /\
      LENGTH lm = LENGTH le /\ LENGTH lm = LENGTH lk /\
      LENGTH rm = LENGTH re /\ LENGTH rm = LENGTH rk` by
    (gen_tac >> strip_tac >>
     `i < LENGTH b` by decide_tac >>
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
         irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 1 insertion_parent_split)) >>
         simp[] >> qexistsl [`seed`,`m'`] >> simp[] >> metis_tac[]) >>
     conj_tac
     >- (simp[NoAsms,Abbr `mb`] >>
         irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 2 insertion_parent_split)) >>
         simp[] >> qexists_tac `seed` >> metis_tac[pairTheory.PAIR_EQ]) >>
     conj_tac
     >- (simp[NoAsms,Abbr `sa`] >>
         qpat_assum `EL (EL i inds) ss = _` (fn th => once_rewrite_tac[GSYM th]) >>
         irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 1 insertion_parent_split)) >>
         metis_tac[]) >>
     conj_tac
     >- (simp[NoAsms,Abbr `sb`] >>
         irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 2 insertion_parent_split)) >>
         simp[] >> qexists_tac `seed` >> metis_tac[pairTheory.PAIR_EQ]) >>
     conj_tac
     >- (simp[NoAsms,Abbr `ka`] >>
         qpat_assum `EL (EL i inds) ks = _` (fn th => once_rewrite_tac[GSYM th]) >>
         irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 1 insertion_parent_split)) >>
         metis_tac[]) >>
     conj_tac
     >- (simp[NoAsms,Abbr `kb`] >>
         irule (PURE_REWRITE_RULE [APPEND_ASSOC] (cj 2 insertion_parent_split)) >>
         simp[] >> qexists_tac `seed` >> metis_tac[pairTheory.PAIR_EQ]) >>
     `LIST_REL (\x y. LENGTH x = LENGTH y) ms ss /\
      LIST_REL (\x y. LENGTH x = LENGTH y) ms ks` by metis_tac[optionTheory.SOME_11] >>
     imp_res_tac insertion_flat_lengths >>
     `!fs. (!f. MEM f fs ==> MEM f (EL (SUC i) orders)) ==>
       LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP (SUC i) b,f)))) fs)) =
       LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP s (DROP (SUC i) b,f)))) fs)) /\
       LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP m (DROP (SUC i) b,f)))) fs)) =
       LENGTH (FLAT (MAP (\f. FLAT (THE (FLOOKUP k (DROP (SUC i) b,f)))) fs))` by
       (gen_tac >> strip_tac >> conj_tac >>
        irule insertion_aggregate_lengths >> metis_tac[]) >>
     qpat_assum `!fs. _` (qspec_then `ds` mp_tac) >>
     qpat_x_assum `!fs. _` (qspec_then `later` mp_tac) >>
     simp[] >> rpt strip_tac >> metis_tac[]) >>
  `mb 0 = FLAT cm /\ sb 0 = FLAT ce /\ kb 0 = FLAT ck` by
    simp[Abbr `mb`,Abbr `sb`,Abbr `kb`,LENGTH_NON_NIL] >>
  drule_all call_insertion_chain >>
  simp[Abbr `ma`,Abbr `mb`,Abbr `sa`,Abbr `sb`,Abbr `ka`,Abbr `kb`]
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
  rpt gen_tac >>
  disch_then (fn th =>
    mp_tac (MATCH_MP dft_packet_call_path_insertion_at_level th) >>
    strip_assume_tac th) >>
  disch_then (qspec_then `LENGTH b` mp_tac) >>
  simp[LENGTH_NON_NIL]
QED
