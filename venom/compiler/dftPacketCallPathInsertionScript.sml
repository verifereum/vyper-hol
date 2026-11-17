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
  first_x_assum drule >>
  disch_then (qx_choose_then `lm` (qx_choose_then `rm`
    (qx_choose_then `le` (qx_choose_then `re`
    (qx_choose_then `lk` (qx_choose_then `rk` strip_assume_tac)))))) >>
  qexistsl [`am ++ lm`,`rm ++ bm`,`ae ++ le`,`re ++ be`,`ak ++ lk`,`rk ++ bk`] >>
  simp[APPEND_ASSOC]
QED
