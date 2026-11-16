Theory dftPacketCallUpdate
Ancestors
  dftPacketTableSplice list rich_list finite_map prim_rec arithmetic pred_set
  frameJointTransition dftGasFromListTraceDefs

Theorem dft_packet_path_sequence_frame[local]:
  !b L seed tab vals ts.
    LENGTH ts = SUC L /\
    EL 0 ts = tab |+ ((b,seed),initial) /\
    (!i. i < L ==>
      EL (SUC i) ts = EL i ts |+
        ((DROP (SUC i) b,FST (EL i b)),vals i (EL i ts))) ==>
    !i. i <= L ==> !a e.
      (a,e) <> (b,seed) /\
      (!r. r < i ==> (a,e) <> (DROP (SUC r) b,FST (EL r b))) ==>
      FLOOKUP (EL i ts) (a,e) = FLOOKUP tab (a,e)
Proof
  rpt gen_tac >> strip_tac >> Induct_on `i`
  >- (simp[FLOOKUP_UPDATE] >> (metis_tac[FLOOKUP_UPDATE])) >>
  rpt strip_tac >>
  `i < L` by decide_tac >>
  `EL (SUC i) ts = EL i ts |+
    ((DROP (SUC i) b,FST (EL i b)),vals i (EL i ts))` by metis_tac[] >>
  simp[FLOOKUP_UPDATE] >> first_x_assum irule >> simp[] >> metis_tac[LESS_TRANS,LESS_SUC_REFL]
QED

Theorem dft_packet_path_sequence_stable[local]:
  !b L vals ts.
    L = LENGTH b /\ LENGTH ts = SUC L /\
    (!r. r < L ==>
      EL (SUC r) ts = EL r ts |+
        ((DROP (SUC r) b,FST (EL r b)),vals r (EL r ts))) ==>
    !k i a e. i <= k /\ k <= L /\ L - i <= LENGTH a ==>
      FLOOKUP (EL k ts) (a,e) = FLOOKUP (EL i ts) (a,e)
Proof
  rpt gen_tac >> strip_tac >> Induct_on `k`
  >- simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `i = SUC k` >- simp[] >>
  `i <= k /\ k < L` by decide_tac >>
  `EL (SUC k) ts = EL k ts |+
    ((DROP (SUC k) b,FST (EL k b)),vals k (EL k ts))` by metis_tac[] >>
  `a <> DROP (SUC k) b` by
    (strip_tac >> gvs[] >> decide_tac) >>
  simp[FLOOKUP_UPDATE] >> first_x_assum irule >> simp[]
QED

Theorem dft_packet_suffix_distinct[local]:
  !b:'a list. !i r.
    i <= LENGTH b /\ r <= LENGTH b /\ i <> r ==>
    DROP i b <> DROP r b
Proof
  rpt strip_tac >>
  `LENGTH (DROP i b) = LENGTH (DROP r b)` by metis_tac[] >>
  gvs[]
QED

Theorem dft_packet_path_rows:
  !b:((num # num) list). !L inds orders child_depth initial_rows
    (tab:(((num # num) list # num),'v list list) fmap).
    b <> [] /\ L = LENGTH b /\ LENGTH inds = L /\
    LENGTH orders = SUC L /\ orders <> [] /\ HD orders = [child_depth] /\
    (!i. i < L ==> ?rows.
      FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rows /\
      EL i inds < LENGTH rows) ==>
    ?ts out.
      LENGTH ts = SUC L /\
      EL 0 ts = tab |+ ((b,child_depth),initial_rows) /\ out = EL L ts /\
      (!i. i < L ==>
        EL (SUC i) ts = EL i ts |+
          ((DROP (SUC i) b,FST (EL i b)),
           LUPDATE
             (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL i ts) (DROP i b,f))))
               (EL i orders))) (EL i inds)
             (THE (FLOOKUP (EL i ts) (DROP (SUC i) b,FST (EL i b)))))) /\
      (!i. i < L ==>
        FLOOKUP (EL i ts) (DROP (SUC i) b,FST (EL i b)) =
        FLOOKUP tab (DROP (SUC i) b,FST (EL i b))) /\
      (!i a e. i <= L /\ (a,e) <> (b,child_depth) /\
        (!r. r < i ==> (a,e) <> (DROP (SUC r) b,FST (EL r b))) ==>
        FLOOKUP (EL i ts) (a,e) = FLOOKUP tab (a,e)) /\
      FLOOKUP out (b,child_depth) = SOME initial_rows /\
      (!i rows. i < L /\
        FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rows ==>
        FLOOKUP out (DROP (SUC i) b,FST (EL i b)) =
          SOME (LUPDATE
            (FLAT (MAP (\f. FLAT (THE (FLOOKUP out (DROP i b,f))))
              (EL i orders))) (EL i inds) rows) /\
        (!k. k <= EL i inds ==>
          TAKE k (THE (FLOOKUP out (DROP (SUC i) b,FST (EL i b)))) =
          TAKE k rows) /\
        (!r. r < LENGTH rows /\ r <> EL i inds ==>
          EL r (THE (FLOOKUP out (DROP (SUC i) b,FST (EL i b)))) = EL r rows) /\
        LENGTH (THE (FLOOKUP out (DROP (SUC i) b,FST (EL i b)))) = LENGTH rows) /\
      FDOM out = FDOM tab UNION {(b,child_depth)}
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `rowval = \i (t:(((num # num) list # num),'v list list) fmap).
     LUPDATE
       (FLAT (MAP (\f. FLAT (THE (FLOOKUP t (DROP i b,f)))) (EL i orders)))
       (EL i inds) (THE (FLOOKUP t (DROP (SUC i) b,FST (EL i b))))` >>
  qabbrev_tac `upd = \(t:(((num # num) list # num),'v list list) fmap) i.
    t |+ ((DROP (SUC i) b,FST (EL i b)),rowval i t)` >>
  qabbrev_tac `iter_tab = PRIM_REC (tab |+ ((b,child_depth),initial_rows)) upd` >>
  qabbrev_tac `ts = GENLIST iter_tab (SUC L)` >>
  `LENGTH ts = SUC L /\ EL 0 ts = tab |+ ((b,child_depth),initial_rows) /\
   (!i. i < L ==> EL (SUC i) ts = upd (EL i ts) i)` by
    simp[Abbr `ts`,Abbr `iter_tab`,PRIM_REC_THM] >>
  `!i a e. i <= L /\ (a,e) <> (b,child_depth) /\
    (!r. r < i ==> (a,e) <> (DROP (SUC r) b,FST (EL r b))) ==>
    FLOOKUP (EL i ts) (a,e) = FLOOKUP tab (a,e)` by
    (rpt gen_tac >> strip_tac >> irule dft_packet_path_sequence_frame >>
     qexistsl [`L`,`b`,`initial_rows`,`child_depth`,`rowval`] >>
     simp[Abbr `upd`]) >>
  `!i. i < L ==>
    FLOOKUP (EL i ts) (DROP (SUC i) b,FST (EL i b)) =
    FLOOKUP tab (DROP (SUC i) b,FST (EL i b))` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     conj_tac
     >- (rpt strip_tac >>
         `LENGTH (DROP (SUC i) b) = LENGTH (DROP (SUC r) b)` by metis_tac[] >>
         gvs[]) >>
     strip_tac >> `LENGTH (DROP (SUC i) b) = LENGTH b` by metis_tac[] >> gvs[]) >>
  `!k i a e. i <= k /\ k <= L /\ L-i <= LENGTH a ==>
    FLOOKUP (EL k ts) (a,e) = FLOOKUP (EL i ts) (a,e)` by
    (rpt gen_tac >> strip_tac >> irule dft_packet_path_sequence_stable >>
     simp[] >> qexistsl [`b`,`rowval`] >> simp[Abbr `upd`]) >>
  `FLOOKUP (EL L ts) (b,child_depth) = SOME initial_rows` by
    (`FLOOKUP (EL L ts) (b,child_depth) = FLOOKUP (EL 0 ts) (b,child_depth)` by
       (first_x_assum irule >> simp[]) >> simp[FLOOKUP_UPDATE]) >>
  `!i rows. i < L /\
     FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rows ==>
     FLOOKUP (EL L ts) (DROP (SUC i) b,FST (EL i b)) =
       SOME (LUPDATE
         (FLAT (MAP (\f. FLAT (THE (FLOOKUP (EL L ts) (DROP i b,f))))
           (EL i orders))) (EL i inds) rows)` by
    (rpt strip_tac >>
     `FLOOKUP (EL L ts) (DROP (SUC i) b,FST (EL i b)) =
      FLOOKUP (EL (SUC i) ts) (DROP (SUC i) b,FST (EL i b))` by
       (first_x_assum irule >> simp[]) >>
     `!f. FLOOKUP (EL L ts) (DROP i b,f) = FLOOKUP (EL i ts) (DROP i b,f)` by
       (gen_tac >> first_x_assum irule >> simp[]) >>
     simp[Abbr `upd`,Abbr `rowval`,FLOOKUP_UPDATE]) >>
  `!i. i <= L ==> FDOM (EL i ts) = FDOM tab UNION {(b,child_depth)}` by
    (Induct >- simp[EXTENSION,DISJ_COMM] >> strip_tac >>
     `i < L` by decide_tac >>
     `?rows. FLOOKUP tab (DROP (SUC i) b,FST (EL i b)) = SOME rows` by metis_tac[] >>
     `((DROP (SUC i) b,FST (EL i b))) IN FDOM tab` by
       (gvs[FLOOKUP_DEF,AllCaseEqs()]) >>
     simp[Abbr `upd`,EXTENSION] >> metis_tac[]) >>
  qexistsl [`ts`,`EL L ts`] >>
  simp[Abbr `upd`,Abbr `rowval`] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!i rows. _ ==> FLOOKUP (EL (LENGTH b) ts) _ = _`
    (drule_all_then assume_tac) >>
  simp[dft_packet_row_prefix_splice,EL_LUPDATE]
QED
