Theory dftPacketExistingPathRows
Ancestors
  dftPacketTableSplice list rich_list finite_map prim_rec arithmetic pred_set

Theorem existing_sequence_frame[local]:
  !p L seed tab vals ts.
    LENGTH ts = SUC L /\ EL 0 ts = tab |+ ((p,seed),initial) /\
    (!i. i < L ==> EL (SUC i) ts = EL i ts |+
      ((DROP (SUC i) p,FST (EL i p)),vals i (EL i ts))) ==>
    !i. i <= L ==> !a e.
      (a,e) <> (p,seed) /\
      (!r. r < i ==> (a,e) <> (DROP (SUC r) p,FST (EL r p))) ==>
      FLOOKUP (EL i ts) (a,e) = FLOOKUP tab (a,e)
Proof
  rpt gen_tac >> strip_tac >> Induct_on `i`
  >- (simp[FLOOKUP_UPDATE] >> metis_tac[FLOOKUP_UPDATE]) >>
  rpt strip_tac >> `i < L` by decide_tac >>
  `EL (SUC i) ts = EL i ts |+
    ((DROP (SUC i) p,FST (EL i p)),vals i (EL i ts))` by metis_tac[] >>
  simp[FLOOKUP_UPDATE] >> first_x_assum irule >> simp[] >>
  metis_tac[LESS_TRANS,LESS_SUC_REFL]
QED

Theorem existing_sequence_stable[local]:
  !p L vals ts.
    L = LENGTH p /\ LENGTH ts = SUC L /\
    (!r. r < L ==> EL (SUC r) ts = EL r ts |+
      ((DROP (SUC r) p,FST (EL r p)),vals r (EL r ts))) ==>
    !k i a e. i <= k /\ k <= L /\ L-i <= LENGTH a ==>
      FLOOKUP (EL k ts) (a,e) = FLOOKUP (EL i ts) (a,e)
Proof
  rpt gen_tac >> strip_tac >> Induct_on `k` >- simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `i = SUC k` >- simp[] >>
  `i <= k /\ k < L` by decide_tac >>
  `EL (SUC k) ts = EL k ts |+
    ((DROP (SUC k) p,FST (EL k p)),vals k (EL k ts))` by metis_tac[] >>
  `a <> DROP (SUC k) p` by (strip_tac >> gvs[] >> decide_tac) >>
  simp[FLOOKUP_UPDATE] >> first_x_assum irule >> simp[]
QED

Theorem dft_packet_existing_path_rows:
  !p:((num # num) list). !L inds orders d initial_rows
    (tab:(((num # num) list # num),'v list list) fmap).
    L = LENGTH p /\ LENGTH inds = L /\ LENGTH orders = SUC L /\
    (!i. i < L ==> ?rows.
      FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows /\
      EL i inds < LENGTH rows) ==>
    ?ts out.
      LENGTH ts = SUC L /\
      EL 0 ts = tab |+ ((p,d),initial_rows) /\ out = EL L ts /\
      (!i. i < L ==>
        EL (SUC i) ts = EL i ts |+
          ((DROP (SUC i) p,FST (EL i p)),
           LUPDATE
             (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i ts) (DROP i p,f))))
               (EL i orders))) (EL i inds)
             (THE (FLOOKUP (EL i ts) (DROP (SUC i) p,FST (EL i p)))))) /\
      (!i. i < L ==>
        FLOOKUP (EL i ts) (DROP (SUC i) p,FST (EL i p)) =
        FLOOKUP tab (DROP (SUC i) p,FST (EL i p))) /\
      (!i a e. i <= L /\ (a,e) <> (p,d) /\
        (!r. r < i ==> (a,e) <> (DROP (SUC r) p,FST (EL r p))) ==>
        FLOOKUP (EL i ts) (a,e) = FLOOKUP tab (a,e)) /\
      FLOOKUP out (p,d) = SOME initial_rows /\
      (!i rows. i < L /\
        FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows ==>
        FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE
            (FLAT (MAP (\f. FLAT (THE (FLOOKUP out (DROP i p,f))))
              (EL i orders))) (EL i inds) rows) /\
        (!k. k <= EL i inds ==>
          TAKE k (THE (FLOOKUP out (DROP (SUC i) p,FST (EL i p)))) =
          TAKE k rows) /\
        (!r. r < LENGTH rows /\ r <> EL i inds ==>
          EL r (THE (FLOOKUP out (DROP (SUC i) p,FST (EL i p)))) = EL r rows) /\
        LENGTH (THE (FLOOKUP out (DROP (SUC i) p,FST (EL i p)))) = LENGTH rows) /\
      FDOM out = FDOM tab UNION {(p,d)}
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `rowval = \i (t:(((num # num) list # num),'v list list) fmap).
     LUPDATE
       (FLAT (MAP (\f. FLAT (THE (FLOOKUP t (DROP i p,f)))) (EL i orders)))
       (EL i inds) (THE (FLOOKUP t (DROP (SUC i) p,FST (EL i p))))` >>
  qabbrev_tac `upd = \(t:(((num # num) list # num),'v list list) fmap) i.
    t |+ ((DROP (SUC i) p,FST (EL i p)),rowval i t)` >>
  qabbrev_tac `iter_tab = PRIM_REC (tab |+ ((p,d),initial_rows)) upd` >>
  qabbrev_tac `ts = GENLIST iter_tab (SUC L)` >>
  `LENGTH ts = SUC L /\ EL 0 ts = tab |+ ((p,d),initial_rows) /\
   (!i. i < L ==> EL (SUC i) ts = upd (EL i ts) i)` by
    simp[Abbr `ts`,Abbr `iter_tab`,PRIM_REC_THM] >>
  `!i a e. i <= L /\ (a,e) <> (p,d) /\
    (!r. r < i ==> (a,e) <> (DROP (SUC r) p,FST (EL r p))) ==>
    FLOOKUP (EL i ts) (a,e) = FLOOKUP tab (a,e)` by
    (rpt gen_tac >> strip_tac >> irule existing_sequence_frame >>
     qexistsl [`L`,`initial_rows`,`p`,`d`,`rowval`] >> simp[Abbr `upd`]) >>
  `!i. i < L ==>
    FLOOKUP (EL i ts) (DROP (SUC i) p,FST (EL i p)) =
    FLOOKUP tab (DROP (SUC i) p,FST (EL i p))` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     conj_tac
     >- (rpt strip_tac >>
         `LENGTH (DROP (SUC i) p) = LENGTH (DROP (SUC r) p)` by metis_tac[] >> gvs[]) >>
     strip_tac >> `LENGTH (DROP (SUC i) p) = LENGTH p` by metis_tac[] >> gvs[]) >>
  `!k i a e. i <= k /\ k <= L /\ L-i <= LENGTH a ==>
    FLOOKUP (EL k ts) (a,e) = FLOOKUP (EL i ts) (a,e)` by
    (rpt gen_tac >> strip_tac >> irule existing_sequence_stable >>
     simp[] >> qexistsl [`p`,`rowval`] >> simp[Abbr `upd`]) >>
  `FLOOKUP (EL L ts) (p,d) = SOME initial_rows` by
    (`FLOOKUP (EL L ts) (p,d) = FLOOKUP (EL 0 ts) (p,d)` by
       (first_x_assum irule >> simp[]) >> simp[FLOOKUP_UPDATE]) >>
  `!i rows. i < L /\
     FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows ==>
     FLOOKUP (EL L ts) (DROP (SUC i) p,FST (EL i p)) =
       SOME (LUPDATE
         (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL L ts) (DROP i p,f))))
           (EL i orders))) (EL i inds) rows)` by
    (rpt strip_tac >>
     `FLOOKUP (EL L ts) (DROP (SUC i) p,FST (EL i p)) =
      FLOOKUP (EL (SUC i) ts) (DROP (SUC i) p,FST (EL i p))` by
       (first_x_assum irule >> simp[]) >>
     `!f. FLOOKUP (EL L ts) (DROP i p,f) = FLOOKUP (EL i ts) (DROP i p,f)` by
       (gen_tac >> first_x_assum irule >> simp[]) >>
     simp[Abbr `upd`,Abbr `rowval`,FLOOKUP_UPDATE]) >>
  `!i. i <= L ==> FDOM (EL i ts) = FDOM tab UNION {(p,d)}` by
    (Induct >- simp[EXTENSION,DISJ_COMM] >> strip_tac >> `i < L` by decide_tac >>
     `?rows. FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows` by metis_tac[] >>
     `((DROP (SUC i) p,FST (EL i p))) IN FDOM tab` by
       gvs[FLOOKUP_DEF,AllCaseEqs()] >>
     simp[Abbr `upd`,EXTENSION] >> metis_tac[]) >>
  qexistsl [`ts`,`EL L ts`] >> simp[Abbr `upd`,Abbr `rowval`] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!i rows. _ ==> FLOOKUP (EL (LENGTH p) ts) _ = _`
    (drule_all_then assume_tac) >>
  simp[dft_packet_row_prefix_splice,EL_LUPDATE]
QED

Theorem existing_aggregate_insert[local]:
  !order e a (rows:'v list list) q v child ins left right tab out.
    ALL_DISTINCT order /\ MEM e order /\
    FLOOKUP tab (a,e) = SOME rows /\ q < LENGTH rows /\
    FLOOKUP out (a,e) = SOME (LUPDATE v q rows) /\
    (!f. MEM f order /\ f <> e ==> FLOOKUP out (a,f) = FLOOKUP tab (a,f)) /\
    EL q rows = child /\ child = left ++ right /\ v = left ++ ins ++ right ==>
    ?l r.
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) order) = l ++ r /\
      FLAT (MAP (\f. FLAT (THE (FLOOKUP out (a,f)))) order) = l ++ ins ++ r
Proof
  rpt gen_tac >> strip_tac >>
  `?ds later. order = ds ++ e::later` by metis_tac[MEM_SPLIT] >>
  gvs[ALL_DISTINCT_APPEND] >>
  `MAP (\f. FLAT (THE (FLOOKUP out (a,f)))) ds =
   MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) ds` by
    (irule MAP_CONG >> simp[] >> metis_tac[]) >>
  `MAP (\f. FLAT (THE (FLOOKUP out (a,f)))) later =
   MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) later` by
    (irule MAP_CONG >> simp[] >> metis_tac[]) >>
  `FLAT rows = FLAT (TAKE q rows) ++ (left ++ right) ++ FLAT (DROP (SUC q) rows)` by
    metis_tac[TAKE_DROP_SUC,FLAT_APPEND,FLAT,APPEND_NIL] >>
  `LUPDATE (left ++ ins ++ right) q rows =
    TAKE q rows ++ [left ++ ins ++ right] ++ DROP (SUC q) rows` by
    (qsuff_tac `!(rs:'v list list) n x. n < LENGTH rs ==>
       LUPDATE x n rs = TAKE n rs ++ [x] ++ DROP (SUC n) rs`
     >- metis_tac[] >>
     Induct >- simp[] >> rpt gen_tac >> Cases_on `n` >> simp[LUPDATE_def]) >>
  qexistsl [`FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) ds) ++
      FLAT (TAKE q rows) ++ left`,
    `right ++ FLAT (DROP (SUC q) rows) ++
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) later)`] >>
  simp[MAP_APPEND,FLAT_APPEND,APPEND_ASSOC]
QED

Theorem dft_packet_existing_path_splice:
  !p:((num # num) list). !L inds orders d (initial_rows:'v list list)
    tab out A A' ds.
    L = LENGTH p /\ LENGTH inds = L /\ LENGTH orders = SUC L /\
    A = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (a,e))))
      (EL (LENGTH p - LENGTH a) orders))) /\
    A' = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP out (a,e))))
      (EL (LENGTH p - LENGTH a) orders))) /\
    (!i. i <= L ==> ALL_DISTINCT (EL i orders)) /\
    EL 0 orders = ds ++ [d] /\ FLOOKUP tab (p,d) = SOME [] /\
    FLOOKUP out (p,d) = SOME initial_rows /\
    (!a e. (a,e) <> (p,d) /\
      (!r. r < L ==> (a,e) <> (DROP (SUC r) p,FST (EL r p))) ==>
      FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
    (!i. i < L ==> MEM (FST (EL i p)) (EL (SUC i) orders) /\
      ?rows. FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows /\
        EL i inds < LENGTH rows /\ EL (EL i inds) rows = A (DROP i p)) /\
    (!i rows. i < L /\
      FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows ==>
      FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
        SOME (LUPDATE (A' (DROP i p)) (EL i inds) rows) /\
      (!k. k <= EL i inds ==>
        TAKE k (THE (FLOOKUP out (DROP (SUC i) p,FST (EL i p)))) = TAKE k rows) /\
      (!r. r < LENGTH rows /\ r <> EL i inds ==>
        EL r (THE (FLOOKUP out (DROP (SUC i) p,FST (EL i p)))) = EL r rows) /\
      LENGTH (THE (FLOOKUP out (DROP (SUC i) p,FST (EL i p)))) = LENGTH rows) ==>
    (?left right. A [] = left ++ right /\
      A' [] = left ++ FLAT initial_rows ++ right) /\
    (!a. (!e. MEM e (EL (LENGTH p - LENGTH a) orders) ==>
       (a,e) <> (p,d) /\
       (!r. r < L ==> (a,e) <> (DROP (SUC r) p,FST (EL r p)))) ==>
       A' a = A a)
Proof
  rpt gen_tac >> strip_tac >>
  `!i f. i <= L /\ (if i = 0 then f <> d else f <> FST (EL (i-1) p)) ==>
     FLOOKUP out (DROP i p,f) = FLOOKUP tab (DROP i p,f)` by
    (rpt gen_tac >> strip_tac >> first_x_assum irule >>
     reverse conj_tac
     >- (strip_tac >>
         `LENGTH (DROP i p) = LENGTH p` by metis_tac[pairTheory.PAIR_EQ] >>
         gvs[] >> Cases_on `i = 0` >> gvs[]) >>
     rpt strip_tac >>
     `LENGTH (DROP i p) = LENGTH (DROP (SUC r) p)` by metis_tac[pairTheory.PAIR_EQ] >>
     `i = SUC r` by (gvs[] >> decide_tac) >> gvs[]) >>
  `!i. i <= L ==> ?left right.
      A (DROP i p) = left ++ right /\
      A' (DROP i p) = left ++ FLAT initial_rows ++ right` by
    (Induct
     >- (strip_tac >>
         `MAP (\f. FLAT (THE (FLOOKUP out (p,f)))) ds =
          MAP (\f. FLAT (THE (FLOOKUP tab (p,f)))) ds` by
           (irule MAP_CONG >> simp[] >> rpt strip_tac >> rename1 `MEM f ds` >>
            `f <> d` by (qpat_x_assum `!i. i <= L ==> ALL_DISTINCT _`
              (qspec_then `0` mp_tac) >> simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
            `FLOOKUP out (p,f) = FLOOKUP tab (p,f)` by
              (qpat_x_assum `!i f. _` (qspecl_then [`0`,`f`] mp_tac) >> simp[]) >> simp[]) >>
         qexistsl [`FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (p,f)))) ds)`,`[]`] >>
         fs[MAP_APPEND,FLAT_APPEND]) >>
     strip_tac >> `i < L` by decide_tac >>
     `?left right. A (DROP i p) = left ++ right /\
       A' (DROP i p) = left ++ FLAT initial_rows ++ right` by
       (qpat_x_assum `i <= L ==> _` irule >> decide_tac) >>
     `MEM (FST (EL i p)) (EL (SUC i) orders) /\
       ?rows. FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME rows /\
       EL i inds < LENGTH rows /\ EL (EL i inds) rows = A (DROP i p)` by metis_tac[] >>
     `FLOOKUP out (DROP (SUC i) p,FST (EL i p)) =
       SOME (LUPDATE (A' (DROP i p)) (EL i inds) rows)` by metis_tac[] >>
     `LENGTH p - LENGTH (DROP (SUC i) p) = SUC i` by (simp[] >> decide_tac) >>
     simp[] >>
     qpat_assum `FLOOKUP tab (DROP (SUC i) p,_) = SOME rows`
       (mp_then Any mp_tac existing_aggregate_insert) >>
     disch_then irule >> simp[] >>
     qexistsl [`left`,`EL i inds`,`right`] >> simp[]) >>
  conj_tac >- (first_x_assum (qspec_then `L` mp_tac) >> simp[]) >>
  rpt strip_tac >> simp[] >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >> metis_tac[]
QED
