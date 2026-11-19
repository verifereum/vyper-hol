Theory staticAbortOptConditionalJumpsTable
Ancestors
  staticAbortOptConditionalJumpsArms asmOptimizer asmSplice asmIR asmSem
  staticAbortStraight finite_map pred_set list arithmetic pair words alist

(* Encode occurrences, not projected PCs. The second band is reserved for
   the strict initial visit and cannot alias an ordinary visit. *)
Theorem conditional_port_wiring[local]:
  !keep D (e:num#num) initial (z0:num#num->num#num) z1 (r:num#num->num) old.
  !Visit. Visit = (\i u. (u IN D /\ i < 4) \/ (initial /\ u=e /\ 4<=i /\ i<8)) ==>
  FINITE keep /\ FINITE D /\ (!u. u IN keep ==> u NOTIN D) /\
  (!u v. u IN keep /\ old u v ==> (v IN keep \/ v IN D) /\ r v < r u) /\
  (!u. u IN D \/ (initial /\ u=e) ==>
     z0 u IN keep /\ z1 u IN keep /\ r (z0 u) < r u /\ r (z1 u) < r u) ==>
  ?copy owner phase (wset:(num#num)->bool) E rank.
    FINITE wset /\
    (!i u. i<8 ==> owner (copy i u)=u /\ phase (copy i u)=i) /\
    (!a. a IN wset ==> phase a<8 /\ a=copy (phase a) (owner a)) /\
    (!i u. i<8 ==> (copy i u IN wset <=> (i=0 /\ u IN keep) \/ Visit i u)) /\
    (!u y. u IN keep ==>
      (E (copy 0 u) y <=> ?v. old u v /\ y=copy 0 v)) /\
    (!i u y. Visit i u ==>
      (E (copy i u) y <=>
         (i MOD 4<3 /\ y=copy (i+1) u) \/
         (i MOD 4=2 /\ y=copy 0 (z0 u)) \/
         (i MOD 4=3 /\ y=copy 0 (z1 u)))) /\
    (!a y. E a y ==> a IN wset /\ y IN wset /\ rank y < (rank a:num))
Proof
  ntac 8 gen_tac >>
  CONV_TAC (HO_REWR_CONV UNWIND_FORALL_THM2) >> simp[] >> strip_tac >>
  qabbrev_tac `copy = \i (u:num#num). (FST u * 8 + i, SND u)` >>
  qabbrev_tac `owner = \a:num#num. (FST a DIV 8, SND a)` >>
  qabbrev_tac `phase = \a:num#num. FST a MOD 8` >>
  qabbrev_tac `Visit = \(i:num) u. (u IN D /\ i<4) \/ (initial /\ u=e /\ 4<=i /\ i<8)` >>
  qabbrev_tac `wset = {a | (phase a=0 /\ owner a IN keep) \/ Visit (phase a) (owner a)}` >>
  qabbrev_tac `rank = \a. 4*r (owner a)+3-(phase a MOD 4)` >>
  qabbrev_tac `E = \a y. a IN wset /\
    if phase a=0 /\ owner a IN keep then ?v. old (owner a) v /\ y=copy 0 v
    else (phase a MOD 4<3 /\ y=copy (phase a+1) (owner a)) \/
         (phase a MOD 4=2 /\ y=copy 0 (z0 (owner a))) \/
         (phase a MOD 4=3 /\ y=copy 0 (z1 (owner a)))` >>
  `!i u. i<8 ==> owner (copy i u)=u /\ phase (copy i u)=i` by
    (rpt gen_tac >> disch_tac >> PairCases_on `u` >>
     simp[Abbr `copy`, Abbr `owner`, Abbr `phase`, DIV_MULT, MOD_MULT, DIV_EQ_0]) >>
  `!a. phase a<8 /\ a=copy (phase a) (owner a)` by
    (simp[Abbr `copy`, Abbr `owner`, Abbr `phase`] >>
     gen_tac >> qspec_then `8` mp_tac DIVISION >> simp[] >>
     disch_then (qspec_then `FST (a:num#num)` mp_tac) >>
     Cases_on `a` >> simp[]) >>
  `!i u. i<8 ==> (copy i u IN wset <=> (i=0 /\ u IN keep) \/ Visit i u)` by
    simp[Abbr `wset`] >>
  `!u y. u IN keep ==> (E (copy 0 u) y <=> ?v. old u v /\ y=copy 0 v)` by
    simp[Abbr `E`] >>
  `!i u y. Visit i u ==>
     (E (copy i u) y <=> (i MOD 4<3 /\ y=copy (i+1) u) \/
      (i MOD 4=2 /\ y=copy 0 (z0 u)) \/ (i MOD 4=3 /\ y=copy 0 (z1 u)))` by
    (rpt strip_tac >> `i<8 /\ ~(i=0 /\ u IN keep)` by
       (gvs[Abbr `Visit`] >> metis_tac[]) >> simp[Abbr `E`]) >>
  `!a. a IN wset ==> owner a IN keep UNION D UNION {e}` by
    simp[Abbr `wset`, Abbr `Visit`, SF DNF_ss] >>
  `FINITE wset` by
    ((irule SUBSET_FINITE >> qexists `IMAGE (UNCURRY copy) (count 8 CROSS (keep UNION D UNION {e}))` >>
     simp[SUBSET_DEF, IN_IMAGE, PULL_EXISTS] >>
     rpt strip_tac >> rename1 `a IN wset` >>
     qexists `(phase a, owner a)` >> simp[] >>
     first_assum (drule_then mp_tac) >> simp[] >> (gvs[SUBSET_DEF, IN_IMAGE, PULL_EXISTS, SUBSET_FINITE]))) >>
  `!a. a IN wset /\ ~(phase a=0 /\ owner a IN keep) ==>
       Visit (phase a) (owner a)` by
    (simp[Abbr `wset`] >> metis_tac[]) >>
  `!a y. E a y ==> a IN wset /\ y IN wset /\ rank y < rank a` by
    (rpt gen_tac >>
     Cases_on `phase a=0 /\ owner a IN keep`
     >- (simp[Abbr `E`, PULL_EXISTS] >> rpt strip_tac >>
         rename1 `old (owner a) v` >>
         qpat_assum `!u v. u IN keep /\ old u v ==> _`
           (qspecl_then [`owner a`, `v`] mp_tac) >>
         simp[Abbr `Visit`, Abbr `rank`]) >>
     disch_tac >>
     `a IN wset` by metis_tac[Abbr `E`] >>
     `Visit (phase a) (owner a)` by
       (qpat_assum `!a. a IN wset /\ ~_ ==> Visit _ _` irule >>
        conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     qpat_x_assum `E a y` mp_tac >> simp[Abbr `E`] >>
     `z0 (owner a) IN keep /\ z1 (owner a) IN keep /\
      r (z0 (owner a)) < r (owner a) /\ r (z1 (owner a)) < r (owner a)` by
        (fs[Abbr `Visit`] >> metis_tac[]) >>
     qpat_x_assum `!u. _ ==> z0 u IN keep /\ _` kall_tac >>
     `phase a<8` by simp[] >>
     `phase a=0 \/ phase a=1 \/ phase a=2 \/ phase a=3 \/
      phase a=4 \/ phase a=5 \/ phase a=6 \/ phase a=7` by decide_tac >>
     fs[Abbr `Visit`] >> strip_tac >> gvs[Abbr `rank`]) >>
  qexistsl [`copy`,`owner`,`phase`,`wset`,`E`,`rank`] >>
  rpt conj_tac >> simp[] >> metis_tac[]
QED

(* Invariants propagate along the same finite paths used in the certificate. *)
Theorem port_reachable_invariant[local]:
  !(E:(num#num)->(num#num)->bool) root (P:(num#num)->bool).
  P root /\ (!a y. P a /\ E a y ==> P y) ==>
  !a. (?n (path:num->num#num).
    path 0 = root /\ path n = a /\ !k. k<n ==> E (path k) (path(SUC k))) ==>
    P a
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  disch_then (qx_choose_then `n` (qx_choose_then `path` strip_assume_tac)) >>
  `!j. j <= n ==> P (path j)` by
    (Induct >> simp[] >> strip_tac >>
     `j < n /\ j <= n` by decide_tac >> metis_tac[]) >>
  metis_tac[LESS_EQ_REFL]
QED

Theorem port_reachable_extension[local]:
  !(E:(num#num)->(num#num)->bool) root a y.
  (?n (path:num->num#num).
    path 0=root /\ path n=a /\ !k. k<n ==> E (path k) (path(SUC k))) /\ E a y ==>
  ?n (path:num->num#num).
    path 0=root /\ path n=y /\ !k. k<n ==> E (path k) (path(SUC k))
Proof
  rpt gen_tac >> strip_tac >>
  qexistsl [`SUC n`, `\k. if k<=n then path k else y`] >>
  simp[] >> rpt strip_tac >> Cases_on `k<n`
  >- (`SUC k <= n` by decide_tac >> simp[]) >>
  `k = n` by decide_tac >> simp[]
QED

Theorem port_reachable_restriction[local]:
  !(family:(num#num)->bool) E root (rank:(num#num)->num)
    (raw:(num#num)->num->(string#num)option) b.
  !Reach. Reach = (\E root a. ?n (path:num->num#num).
    path 0=root /\ path n=a /\ !k. k<n ==> E (path k) (path(SUC k))) ==>
  !active. active = {a | a IN family /\ Reach E root a} ==>
  FINITE family /\ root IN family /\
  (!a y. E a y ==> a IN family /\ y IN family /\ rank y < rank a) /\
  (!a y k l. E a y /\ raw y k=SOME(l,b) ==> ?j. raw a j=SOME(l,b)) ==>
  FINITE active /\ root IN active /\
  (!a. a IN active ==> Reach E root a) /\
  (!a y. a IN active /\ E a y ==> y IN active /\ rank y < rank a) /\
  (!a k l. a IN active /\ raw a k=SOME(l,b) ==> ?j. raw root j=SOME(l,b))
Proof
  ntac 6 gen_tac >>
  CONV_TAC (TOP_DEPTH_CONV (FIRST_CONV [HO_REWR_CONV UNWIND_FORALL_THM2, BETA_CONV])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (irule SUBSET_FINITE >> qexists `family` >> simp[SUBSET_DEF]) >>
  simp[] >> conj_tac
  >- (qexistsl [`0`, `\n:num. root`] >> simp[]) >>
  conj_tac >- metis_tac[port_reachable_extension] >>
  `!a. (?n (path:num->num#num).
    path 0=root /\ path n=a /\ !k. k<n ==> E (path k) (path(SUC k))) ==>
    !k l. raw a k=SOME(l,b) ==> ?j. raw root j=SOME(l,b)` by
    (ho_match_mp_tac port_reachable_invariant >> metis_tac[]) >>
  metis_tac[]
QED

(* A reached visit has both retained exits in the same closed active set. *)
Theorem port_visit_exits_reached[local]:
  !D (e:num#num) initial keep copy owner phase family E root A z0 z1.
  !Visit. Visit = (\i u. (u IN D /\ i<4) \/ (initial /\ u=e /\ 4<=i /\ i<8)) ==>
  !Reach. Reach = (\a. ?n (path:num->num#num).
    path 0=root /\ path n=a /\ !k. k<n ==> E (path k) (path(SUC k))) ==>
  (!i u. i<8 ==> owner (copy i u)=u /\ phase (copy i u)=i) /\
  (!a. a IN family ==> phase a<8 /\ a=copy (phase a) (owner a) /\
      ((phase a=0 /\ owner a IN keep) \/ Visit (phase a) (owner a))) /\
  (!u y. u IN keep /\ E (copy 0 u) y ==> ?v. y=copy 0 v) /\
  (!i u y. Visit i u ==> (E (copy i u) y <=>
     (i MOD 4<3 /\ y=copy (i+1) u) \/
     (i MOD 4=2 /\ y=copy 0 (z0 u)) \/ (i MOD 4=3 /\ y=copy 0 (z1 u)))) /\
  A SUBSET family /\ root IN A /\ (?i u. (i=0 \/ i=4) /\ root=copy i u) /\
  (!a. a IN A ==> Reach a) /\ (!a y. a IN A /\ E a y ==> y IN A) ==>
  !a. a IN A /\ Visit (phase a) (owner a) ==>
     copy 0 (z0 (owner a)) IN A /\ copy 0 (z1 (owner a)) IN A
Proof
  ntac 13 gen_tac >>
  map_every (fn v => qx_gen_tac v >>
    disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]))
    [`Visit`,`Reach`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!u i. (i=0 \/ i=4) /\ copy i u IN A /\ Visit i u ==>
       copy 0 (z0 u) IN A /\ copy 0 (z1 u) IN A` by
     suspend "entrance" >>
  qabbrev_tac `Good = \a. a IN A /\ (Visit (phase a) (owner a) ==>
       copy 0 (z0 (owner a)) IN A /\ copy 0 (z1 (owner a)) IN A)` >>
  `!u i. (i=0 \/ i=4) /\ copy i u IN A ==> Good (copy i u)` by
    (rpt gen_tac >> strip_tac >> simp[Abbr `Good`] >> metis_tac[]) >>
  `Good root` by metis_tac[] >>
  `!a y. Good a /\ E a y ==> Good y` by suspend "step" >>
  `!a. Reach a ==> Good a` by
    (simp[Abbr `Reach`] >> ho_match_mp_tac port_reachable_invariant >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  metis_tac[Abbr `Good`, Abbr `Reach`]
QED

Resume port_visit_exits_reached[entrance]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!j. j<4 ==> Visit (i+j) u /\ (i+j) MOD 4=j` by
    (gen_tac >> disch_tac >> `j=0 \/ j=1 \/ j=2 \/ j=3` by decide_tac >>
     gvs[Abbr `Visit`]) >>
  `!j. j<4 ==> copy (i+j) u IN A` by
    (Induct >- simp[] >> disch_tac >>
     `j<4 /\ j<3` by (qpat_assum `SUC j < 4` mp_tac >> decide_tac) >>
     `copy (i+j) u IN A` by metis_tac[] >>
     `Visit (i+j) u /\ (i+j) MOD 4=j` by metis_tac[] >>
     `E (copy (i+j) u) (copy ((i+j)+1) u)` by simp[] >>
     rewrite_tac[ADD1, ADD_ASSOC] >> metis_tac[ADD_ASSOC]) >>
  `E (copy (i+2) u) (copy 0 (z0 u)) /\ E (copy (i+3) u) (copy 0 (z1 u))` by simp[] >>
  metis_tac[DECIDE ``2<4n /\ 3<4n``]
QED

Resume port_visit_exits_reached[step]:
  rpt gen_tac >> strip_tac >>
  `a IN A /\ y IN A /\ a IN family` by metis_tac[Abbr `Good`, SUBSET_DEF] >>
  qpat_assum `!a. a IN family ==> phase a<8 /\ _`
    (qspec_then `a` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `phase a=0 /\ owner a IN keep`
  >- (`?v. y=copy 0 v` by metis_tac[] >> metis_tac[]) >>
  `Visit (phase a) (owner a)` by metis_tac[] >>
  qpat_assum `!i u y. Visit i u ==> (E (copy i u) y <=> _)`
    (qspecl_then [`phase a`,`owner a`,`y`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `a=copy _ _` (fn th => once_rewrite_tac[GSYM th]) >>
  simp[] >> strip_tac
  >- (`phase a+1<8` by
        (Cases_on `phase a=7`
         >- (qpat_x_assum `phase a MOD 4 < 3` mp_tac >> simp[]) >>
         qpat_assum `phase a<8` mp_tac >> qpat_assum `phase a<>7` mp_tac >> decide_tac) >>
      `owner y=owner a` by metis_tac[] >>
      qpat_assum `Abbrev (Good=_)` (fn d =>
        qpat_assum `Good a` (mp_tac o BETA_RULE o
          REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] d])) >>
      simp[Abbr `Good`]) >>
  qpat_assum `!u i. _ ==> Good (copy i u)` (fn th =>
    qpat_assum `y=copy 0 _` SUBST1_TAC >> irule th >>
    gvs[])
QED

Finalise port_visit_exits_reached

(* Raw annotations for the four rows of a visit. The fresh PUSH is
   recorded at the OLD origin b+2, even though its new PC is b+1. *)
Theorem visit_raw_deleted_origin[local]:
  !b label (left:num->(string#num)option) right.
  !union. union = (\k. case left k of NONE => right k | SOME t => SOME t) ==>
  !raw. raw = (\(i:num) k.
    if i<2 then (if k=0 then NONE else union (k-1)) else
    if i=2 then (if k=0 then SOME(label,b+2) else if k=1 then NONE else union (k-2))
    else right k) ==>
  (!k t s. left k=SOME t /\ right k=SOME s ==> t=s) ==>
  (!i k l. i<3 /\ raw (i+1) k=SOME(l,b) ==> ?j. raw i j=SOME(l,b)) /\
  (!k l. left k=SOME(l,b) ==> ?j. raw 2 j=SOME(l,b)) /\
  (!k l. right k=SOME(l,b) ==> ?j. raw 3 j=SOME(l,b))
Proof
  ntac 4 gen_tac >>
  CONV_TAC (TOP_DEPTH_CONV (FIRST_CONV [HO_REWR_CONV UNWIND_FORALL_THM2, BETA_CONV])) >>
  simp_tac (srw_ss()) [] >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> `i=0 \/ i=1 \/ i=2` by decide_tac >>
      gvs[]
      >- (qexists `k` >> simp[])
      >- (qexists `k-1` >> gvs[AllCaseEqs()] >> decide_tac) >>
      qexists `k+2` >> Cases_on `left k` >> gvs[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> qexists `k+2` >> simp[]) >>
  rpt strip_tac >> qexists `k` >> Cases_on `left k` >> gvs[] >> metis_tac[]
QED

(* A visit entrance only thins the old annotation, including when the
   union chooses the taken port in preference to the fall port. *)
Theorem visit_entrance_raw_inclusion[local]:
  !(tag:(num#num)->num->(string#num)option) u z0 z1 k t.
  (!k t. tag z0 k=SOME t ==> tag u (k+1)=SOME t) /\
  (!k t. tag z1 k=SOME t ==> tag u (k+1)=SOME t) /\
  (if k=0 then NONE else
     case tag z0 (k-1) of NONE => tag z1 (k-1) | SOME s => SOME s) = SOME t ==>
  tag u k=SOME t
Proof
  rpt gen_tac >> Cases_on `k` >> simp[] >>
  Cases_on `tag z0 n` >> simp[GSYM ADD1] >> rpt strip_tac >>
  first_x_assum (drule_then MATCH_ACCEPT_TAC)
QED

(* Trace the deleted producer through the port table before choosing rho. *)
Theorem port_table_raw_predecessor[local]:
  !keep D (e:num#num) initial z0 z1 old copy owner phase family E
    (tag:(num#num)->num->(string#num)option) b label.
  !Visit. Visit = (\i u. (u IN D /\ i < 4) \/ (initial /\ u=e /\ 4<=i /\ i<8)) ==>
  !U. U = (\u k. case tag (z0 u) k of NONE => tag (z1 u) k | SOME t => SOME t) ==>
  !vraw. vraw = (\u (i:num) k.
    if i<2 then (if k=0 then NONE else U u (k-1)) else
    if i=2 then (if k=0 then SOME(label,b+2) else if k=1 then NONE else U u (k-2))
    else tag (z1 u) k) ==>
  !raw. raw = (\a. if phase a=0 /\ owner a IN keep then tag (owner a)
    else vraw (owner a) (phase a MOD 4)) ==>
  (!i u. i<8 ==> owner (copy i u)=u /\ phase (copy i u)=i) /\
  (!a. a IN family ==> phase a<8 /\ a=copy (phase a) (owner a) /\
       ((phase a=0 /\ owner a IN keep) \/ Visit (phase a) (owner a))) /\
  (!u y. u IN keep ==> (E (copy 0 u) y <=> ?v. old u v /\ y=copy 0 v)) /\
  (!i u y. Visit i u ==>
      (E (copy i u) y <=> (i MOD 4<3 /\ y=copy (i+1) u) \/
       (i MOD 4=2 /\ y=copy 0 (z0 u)) \/ (i MOD 4=3 /\ y=copy 0 (z1 u)))) /\
  (!a y. E a y ==> a IN family /\ y IN family) /\
  (!u v k l. u IN keep /\ old u v /\ tag v k=SOME(l,b) ==> ?j. tag u j=SOME(l,b)) /\
  (!u. u IN D \/ (initial /\ u=e) ==>
     z0 u IN keep /\ z1 u IN keep /\
     (!k t s. tag (z0 u) k=SOME t /\ tag (z1 u) k=SOME s ==> t=s) /\
     (u IN D ==> !k t. (tag (z0 u) k=SOME t \/ tag (z1 u) k=SOME t) ==>
                                      tag u (k+1)=SOME t)) ==>
  !a y k l. E a y /\ raw y k=SOME(l,b) ==> ?j. raw a j=SOME(l,b)
Proof
  ntac 15 gen_tac >>
  map_every (fn v => qx_gen_tac v >>
    disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]))
    [`Visit`,`U`,`vraw`,`raw`] >>
  strip_tac >> map_every qx_gen_tac [`a`,`y`,`k`,`l`] >> strip_tac >>
  `!u k t. u IN D /\ vraw u 0 k = SOME t ==> tag u k = SOME t` by
    (rpt strip_tac >> gvs[Abbr `vraw`, Abbr `U`] >>
     qspecl_then [`tag`, `u`, `z0 u`, `z1 u`] mp_tac visit_entrance_raw_inclusion >>
     disch_then (qspecl_then [`k'`, `t`] mp_tac) >> simp[] >> metis_tac[]) >>
  `!u. u IN D \/ (initial /\ u=e) ==>
     (!i k l. i<3 /\ vraw u (i+1) k=SOME(l,b) ==> ?j. vraw u i j=SOME(l,b)) /\
     (!k l. tag (z0 u) k=SOME(l,b) ==> ?j. vraw u 2 j=SOME(l,b)) /\
     (!k l. tag (z1 u) k=SOME(l,b) ==> ?j. vraw u 3 j=SOME(l,b))` by
    (gen_tac >> disch_tac >>
     `!k t s. tag (z0 u) k=SOME t /\ tag (z1 u) k=SOME s ==> t=s` by metis_tac[] >>
     qspecl_then [`b`,`label`,`tag (z0 u)`,`tag (z1 u)`]
       (mp_tac o CONV_RULE (TOP_DEPTH_CONV
         (FIRST_CONV [HO_REWR_CONV UNWIND_FORALL_THM2, BETA_CONV]))) visit_raw_deleted_origin >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[Abbr `vraw`, Abbr `U`]) >>
  `a IN family /\ y IN family` by (first_x_assum drule >> simp[]) >>
  `phase a<8 /\ a=copy (phase a) (owner a)` by
    (qpat_assum `!z. z IN family ==> phase z < 8 /\ _`
      (qspec_then `a` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  Cases_on `phase a=0 /\ owner a IN keep`
  >- suspend "retained" >>
  suspend "visit"
QED

Resume port_table_raw_predecessor[retained]:
  `?v. old (owner a) v /\ y=copy 0 v` by
    (qpat_assum `!u y. u IN keep ==> (E (copy 0 u) y <=> _)`
       (qspecl_then [`owner a`,`y`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `tag v k=SOME(l,b)` by
    (rename1 `y = copy 0 v` >>
     `owner y = v /\ phase y = 0` by metis_tac[DECIDE ``0<8n``] >>
     Cases_on `v IN keep`
     >- gvs[Abbr `raw`] >>
     `v IN D` by
       (qpat_assum `!z. z IN family ==> phase z < 8 /\ _`
         (qspec_then `y` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (mp_tac o CONJUNCT2 o CONJUNCT2) >>
        qpat_assum `phase y = 0` (fn th => rewrite_tac[th]) >>
        qpat_assum `owner y = v` (fn th => rewrite_tac[th]) >>
        simp[Abbr `Visit`]) >>
     `vraw v 0 k = SOME (l,b)` by gvs[Abbr `raw`] >> metis_tac[]) >>
  simp[Abbr `raw`] >> metis_tac[]
QED

Resume port_table_raw_predecessor[visit]:
  `Visit (phase a) (owner a)` by
    (qpat_assum `!z. z IN family ==> phase z < 8 /\ _`
      (qspec_then `a` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >> metis_tac[]) >>
  qpat_assum `!i u y. Visit i u ==> (E (copy i u) y <=> _)`
    (qspecl_then [`phase a`,`owner a`,`y`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `a = copy _ _` (fn th => once_rewrite_tac[GSYM th]) >> simp[] >>
  Q_TAC (fn t => SUBGOAL_THEN t assume_tac) `owner a IN D \/ (initial /\ owner a = e)`
  >- fs[Abbr `Visit`] >>
  `z0 (owner a) IN keep /\ z1 (owner a) IN keep` by metis_tac[] >>
  `!v. v IN keep ==> raw (copy 0 v) = tag v` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i u. i<8 ==> _`
       (qspecl_then [`0`,`v`] mp_tac) >>
     simp[Abbr `raw`]) >>
  strip_tac
  >- (rename1 `phase a MOD 4 < 3` >>
      `phase a+1<8 /\ (phase a+1) MOD 4=phase a MOD 4+1 /\ phase a+1 <> 0` by
        (`phase a=0 \/ phase a=1 \/ phase a=2 \/ phase a=3 \/
          phase a=4 \/ phase a=5 \/ phase a=6 \/ phase a=7` by decide_tac >>
         fs[]) >>
      `owner y = owner a /\ phase y = phase a+1` by metis_tac[] >>
      `vraw (owner a) (phase a MOD 4+1) k = SOME(l,b)` by gvs[Abbr `raw`] >>
      simp[Abbr `raw`] >> metis_tac[])
  >- (`tag (z0 (owner a)) k=SOME(l,b)` by metis_tac[] >>
      simp[Abbr `raw`] >> metis_tac[]) >>
  `tag (z1 (owner a)) k=SOME(l,b)` by metis_tac[] >>
  simp[Abbr `raw`] >> metis_tac[]
QED

Finalise port_table_raw_predecessor

(* Every visit packet uses four internal rows and two interfaces to old
   occurrences. The table identifies those interfaces with retained copies. *)
Theorem conditional_jump_port_table:
  !p q b x V e (rank:(num#num)->num) (pc:(num#num)->num) height need
    (tag:(num#num)->num->(string#num)option) boolean old cc req z z0 z1.
  !r. r = splice_pc b 4 3 ==>
  !C. C = (\p l d. ?off. FLOOKUP (SND(compute_label_offsets p)) l=SOME off /\
                       off<dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off=SOME d) ==>
  !Producer. Producer = (\p l i. i<LENGTH p /\
       (EL i p=AsmPushLabel l \/ EL i p=AsmPushOfst l 0) /\ ?d. C p l d) ==>
  !Slots. Slots = (\p h n tg bl.
    (n ==> cc.cc_static) /\ (!k. bl k ==> k<h /\ tg k=NONE) /\
    (!k l i. tg k=SOME(l,i) ==> k<h /\ Producer p l i)) ==>
  !Flow. Flow = (\p pc height tag boolean (u:num#num) (v:num#num).
    !hi. hi = height u ==>
    !hj. hj = height v ==>
    !ins. ins = EL (pc u) p ==>
    !inherit. inherit = (\(src:num->num option) (fresh:num->(string#num)option) bnew.
      (!k l i. tag v k=SOME(l,i) ==> k<hj /\
        (fresh k=SOME(l,i) \/ ?a. src k=SOME a /\ a<hi /\ tag u a=SOME(l,i))) /\
      (!k. boolean v k ==> k<hj /\ (bnew k \/ ?a. src k=SOME a /\ a<hi /\ boolean u a))) ==>
    case ins of
      AsmLabel l => hj=hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj=hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t s. asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                     (AsmPush bs) t=AsmOK s ==> EL 0 s.as_stack=0w \/ EL 0 s.as_stack=1w)
    | AsmPushLabel l => hj=hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,pc u) else NONE) (\k. F)
    | AsmPushOfst l d => hj=hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,pc u) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n<hi /\ hj=hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0<n /\ n<hi /\ hj=hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k)) (\k. NONE) (\k. F)
           | NONE =>
               !a. a = asm_op_arity name ==>
               !m. m = hj+a-hi ==>
               a<=hi /\ hj=m+(hi-a) /\ ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t s. LENGTH t.as_stack=hi /\
                     asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p) ins t=AsmOK s ==>
                       EL 0 s.as_stack=0w \/ EL 0 s.as_stack=1w))
    | _ => F) ==>
  !Target. Target = (\p tg d. ?l i. tg 0=SOME(l,i) /\ C p l d) ==>
  !Legal. Legal = (\p i tg j.
    if EL i p=AsmOp "JUMP" then Target p tg j else
    if EL i p=AsmOp "JUMPI" then j=i+1 \/ Target p tg j else j=i+1) ==>
  !Row. Row = (\p i h tg (edge:(num#num)->bool) pc height.
    !arm. arm = (\P n. ?v. edge v /\ P (pc v) /\ height v=n) ==>
    !legal. legal = (\P n. !v. edge v ==> P (pc v) /\ height v=n) ==>
    !fall. fall = (\d. d=i+1) ==>
    !taken. taken = Target p tg ==>
    !next. next = (\n. arm fall n /\ legal fall n) ==>
    !untagged. untagged = (\a. !k. k<a ==> tg k=NONE) ==>
    !stop. stop = (\a. a<=h /\ untagged a /\ !v. ~edge v) ==>
    case EL i p of
      AsmLabel l => next h
    | AsmPush bs => next (h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
    | AsmOp name =>
        if name="INVALID" then stop 0 else if name="REVERT" then stop 2 else
        if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"] then
          cc.cc_static /\ stop (asm_op_arity name) else
        (case ALOOKUP dup_table name of
           SOME n => n<h /\ next (h+1)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0<n /\ n<h /\ next h
           | NONE => if name="JUMP" then 1<=h /\ arm taken (h-1) /\ legal taken (h-1) else
                     if name="JUMPI" then 2<=h /\ tg 1=NONE /\ arm fall (h-2) /\
                       arm taken (h-2) /\ legal (\d. fall d \/ taken d) (h-2) else
                     ?m. static_abort_straight name m /\ asm_op_arity name<=h /\
                       untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
    | _ => F) ==>
  !keep. keep = {u | u IN V /\ (pc u<b \/ b+4<=pc u)} ==>
  !D. D = {u | u IN V /\ pc u=b} ==>
  !initial. initial = (pc e=b+1) ==>
  !late. late = (pc e=b+2 \/ pc e=b+3) ==>
  !H. H = (\u. if initial /\ u=e then height u-1 else height u) ==>
  !U. U = (\u k. case tag (z0 u) k of NONE => tag (z1 u) k | SOME t => SOME t) ==>
  !UB. UB = (\u k. boolean (z0 u) k \/ boolean (z1 u) k) ==>
  !vraw. vraw = (\u (i:num) k.
    if i<2 then (if k=0 then NONE else U u (k-1)) else
    if i=2 then (if k=0 then SOME(x,b+2) else if k=1 then NONE else U u (k-2))
    else if i=4 then tag (z0 u) k else tag (z1 u) k) ==>
  !vb. vb = (\u (i:num) k.
    if i=0 then k<>0 /\ UB u (k-1) else if i=1 then k=0 \/ UB u (k-1) else
    if i=2 then k=1 \/ (2<=k /\ UB u (k-2)) else
    if i=4 then boolean (z0 u) k else boolean (z1 u) k) ==>
  !vp. vp = (\u (i:num). if i<4 then b+i else if i=4 then r(pc(z0 u)) else r(pc(z1 u))) ==>
  !vh. vh = (\u (i:num). if i<2 then H u else if i=2 then H u+1 else H u-1) ==>
  !VE. VE = (\(i:num) j. (i<3 /\ j=i+1) \/ (i=2 /\ j=4) \/ (i=3 /\ j=5)) ==>
  !Tr. Tr = (\rho tg k. OPTION_MAP (\(l,i). (l,rho l i)) (tg k)) ==>
  FINITE V /\ e IN V /\
  (!u. u IN V ==> Slots p (height u) (need u) (tag u) (boolean u)) /\
  (!u v. u IN keep /\ old u v ==> (v IN keep \/ v IN D) /\ rank v<rank u) /\
  (!u v k l. u IN keep /\ old u v /\ tag v k=SOME(l,b) ==> ?j. tag u j=SOME(l,b)) /\
  (!l j. C p l j ==> C q l (r j)) /\
  (!l i. Producer p l i ==>
     ((i<b \/ b+4<=i) /\ Producer q l (r i)) \/ (i=b+2 /\ l=x) \/ i=b) /\
  b+3<LENGTH q /\ EL (b+1) q=AsmPushLabel x /\
  (late ==> z IN keep /\ C p x (pc z) /\
    height z=(if pc e=b+3 then height e-1 else height e) /\
    (!k l i. tag z k=SOME(l,i) ==> tag e (if pc e=b+3 then k+1 else k)=SOME(l,i)) /\
    (!k. boolean z k ==> boolean e (if pc e=b+3 then k+1 else k))) /\
  (!u. u IN D \/ (initial /\ u=e) ==>
     0<H u /\ z0 u IN keep /\ z1 u IN keep /\ rank (z0 u)<rank u /\ rank (z1 u)<rank u /\
     height (z0 u)=H u-1 /\ height (z1 u)=H u-1 /\ C p x (pc (z0 u)) /\
     (!k t s. tag (z0 u) k=SOME t /\ tag (z1 u) k=SOME s ==> t=s) /\
     (!k t. (tag (z0 u) k=SOME t \/ tag (z1 u) k=SOME t) ==>
       tag u (if initial /\ u=e then k+2 else k+1)=SOME t) /\
     (!k. UB u k ==> boolean u (if initial /\ u=e then k+2 else k+1)) /\
     (!rho P J T B.
       P = (\v:num#num. vp u (FST v)) /\ J = (\v:num#num. vh u (FST v)) /\
       T = (\(v:num#num) k. if FST v=2 /\ k=0 then SOME(x,b+1) else Tr rho (vraw u (FST v)) k) /\
       B = (\v:num#num. vb u (FST v)) ==>
       (!i j. VE i j ==> Flow q P J T B (i,0) (j,0)) /\
       (C q x (r(pc(z0 u))) /\
        (!v k l i. (v=z0 u \/ v=z1 u) /\ tag v k=SOME(l,i) ==> Producer q l (rho l i)) ==>
        (!i. i<4 ==> Slots q (vh u i) ((i=4 /\ need(z0 u)) \/ (i=5 /\ need(z1 u))) (T (i,0)) (B (i,0))) /\
        (!i. i<4 ==> vp u i<LENGTH q /\ Row q (vp u i) (vh u i) (T (i,0))
                              (\v. VE i (FST v)) P J) /\
        (!i j. VE i j ==> Legal q (vp u i) (T (i,0)) (vp u j))))) /\
  (!u rho. u IN keep /\
     (!l. EL (pc u) p=AsmPushLabel l \/ EL (pc u) p=AsmPushOfst l 0 ==> rho l (pc u)=r(pc u)) ==>
     r(pc u)<LENGTH q /\ Row q (r(pc u)) (height u) (Tr rho (tag u)) (old u) (r o pc) height /\
     (!v. old u v ==> Legal q (r(pc u)) (Tr rho (tag u)) (r(pc v)) /\
        Flow q (r o pc) height
          (\v. if v=u then Tr rho (tag u) else Tr rho (if v IN keep then tag v else vraw v 0))
          (\v. if v=u then boolean u else if v IN keep then boolean v else vb v 0) u v)) ==>
  ?family A root (R:(num#num)->num) P J N raw B E.
    !src. src = (\k. if initial \/ pc e=b+3 then k+1 else k) ==>
    FINITE family /\
    A={a | a IN family /\ ?n (path:num->num#num).
      path 0=root /\ path n=a /\ !k. k<n ==> E (path k) (path(SUC k))} /\
    FINITE A /\ root IN A /\
    (!a y. a IN A /\ E a y ==> y IN A /\ R y<R a) /\
    (!a k l. a IN A /\ raw a k=SOME(l,b) ==> ?j. raw root j=SOME(l,b)) /\
    P root=(if late then r(pc z) else r(pc e)) /\
    J root=(if initial \/ pc e=b+3 then height e-1 else height e) /\
    N root=(if late then need z else if e IN keep then need e else F) /\
    (!k l i. raw root k=SOME(l,i) ==> (initial ==> k<>0) /\ tag e (src k)=SOME(l,i)) /\
    (!k. B root k ==> (initial ==> k<>0) /\ boolean e (src k)) /\
    ((!k l. raw root k=SOME(l,b) ==> ?i. Producer q l i) ==>
     ?rho. !T. T = (\a. Tr rho (raw a)) ==>
       (!a. a IN A ==> Slots q (J a) (N a) (T a) (B a) /\
          (?t:asm_state.
            t.as_pc=P a /\ LENGTH t.as_stack=J a /\ t.as_call_ctx=cc /\ t.as_requests=req /\
            (N a ==> cc.cc_static) /\
            (!k l i. T a k=SOME(l,i) ==> k<J a /\ i<LENGTH q /\
              (EL i q=AsmPushLabel l \/ (?d. EL i q=AsmPushOfst l d) \/ EL i q=AsmDataLabel l) /\
              ?off dst. FLOOKUP (SND(compute_label_offsets q)) l=SOME off /\
                off<dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off=SOME dst /\
                EL k t.as_stack=(n2w off:bytes32)) /\
            (!k. B a k ==> k<J a /\ (EL k t.as_stack=0w \/ EL k t.as_stack=1w))) /\
          P a<LENGTH q /\ Row q (P a) (J a) (T a) (\y. E a y) P J) /\
       (!a y. a IN A /\ E a y ==> Legal q (P a) (T a) (P y) /\ Flow q P J T B a y))
Proof
  ntac 18 gen_tac >>
  map_every (fn v => qx_gen_tac v >>
    CONV_TAC (LAND_CONV (RAND_CONV (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)))) >>
    disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]))
    [`r`,`C`,`Producer`,`Slots`,`Flow`,`Target`,`Legal`,`Row`,`keep`,`D`,`initial`,`late`,
     `H`,`U`,`UB`,`vraw`,`vb`,`vp`,`vh`,`VE`,`Tr`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `Reach = \(edge:(num#num)->(num#num)->bool) root a.
    ?n (path:num->num#num). path 0=root /\ path n=a /\ !k. k<n ==> edge (path k) (path(SUC k))` >>
  qabbrev_tac `Shape = \p h d n tg bl (t:asm_state).
    t.as_pc=d /\ LENGTH t.as_stack=h /\ t.as_call_ctx=cc /\ t.as_requests=req /\
    (n ==> cc.cc_static) /\
    (!k l i. tg k=SOME(l,i) ==> k<h /\ i<LENGTH p /\
       (EL i p=AsmPushLabel l \/ (?a. EL i p=AsmPushOfst l a) \/ EL i p=AsmDataLabel l) /\
       ?off dst. FLOOKUP (SND(compute_label_offsets p)) l=SOME off /\
         off<dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off=SOME dst /\
         EL k t.as_stack=(n2w off:bytes32)) /\
    (!k. bl k ==> k<h /\ (EL k t.as_stack=0w \/ EL k t.as_stack=1w))` >>
  qabbrev_tac `vn = \u (i:num). (i=4 /\ need(z0 u)) \/ (i=5 /\ need(z1 u))` >>
  qabbrev_tac `rt = \u. if u IN keep then tag u else vraw u 0` >>
  qabbrev_tac `rb = \u. if u IN keep then boolean u else vb u 0` >>
  qabbrev_tac `Visit = \(i:num) u. (u IN D /\ i < 4) \/ (initial /\ u=e /\ 4<=i /\ i<8)` >>
  `? (copy:num->(num#num)->num#num) owner phase family E R.
      FINITE family /\
      (!i u. i<8 ==> owner (copy i u)=u /\ phase (copy i u)=i) /\
      (!a. a IN family ==> phase a<8 /\ a=copy (phase a) (owner a)) /\
      (!i u. i<8 ==> (copy i u IN family <=> (i=0 /\ u IN keep) \/ Visit i u)) /\
      (!u y. u IN keep ==> (E (copy 0 u) y <=> ?v. old u v /\ y=copy 0 v)) /\
      (!i u y. Visit i u ==>
        (E (copy i u) y <=> (i MOD 4<3 /\ y=copy (i+1) u) \/
         (i MOD 4=2 /\ y=copy 0 (z0 u)) \/ (i MOD 4=3 /\ y=copy 0 (z1 u)))) /\
      (!a y. E a y ==> a IN family /\ y IN family /\ R y < (R a:num))` by
    (`FINITE keep /\ FINITE D` by
       (conj_tac >> irule SUBSET_FINITE >> qexists `V` >>
        simp[SUBSET_DEF, Abbr `keep`, Abbr `D`]) >>
     qspecl_then [`keep`,`D`,`e`,`initial`,`z0`,`z1`,`rank`,`old`,`Visit`]
       mp_tac conditional_port_wiring >>
     (impl_tac >- simp[Abbr `Visit`]) >>
     impl_tac >- (simp[] >> conj_tac
       >- (simp[Abbr `keep`, Abbr `D`] >> decide_tac) >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!u v. u IN keep /\ old u v ==> _`
           (qspecl_then [`u`,`v`] mp_tac) >> simp[])
     >- (gen_tac >> disch_tac >>
         qpat_assum `!u. u IN D \/ (initial /\ u=e) ==> _`
           (qspec_then `u` mp_tac) >> simp[])) >> simp[]) >>
  `!a. a IN family ==> phase a<8 /\ a=copy (phase a) (owner a) /\
         ((phase a=0 /\ owner a IN keep) \/ Visit (phase a) (owner a))` by
    (gen_tac >> disch_tac >>
     `phase a<8 /\ a=copy (phase a) (owner a)` by metis_tac[] >>
     `copy (phase a) (owner a) IN family` by
       (qpat_assum `a=copy _ _` (fn th => once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!i u. i<8 ==> (_ IN family <=> _)`
       (qspecl_then [`phase a`,`owner a`] mp_tac) >> simp[]) >>
  qabbrev_tac `root = if initial then copy 4 e else if late then copy 0 z else copy 0 e` >>
  qabbrev_tac `isRet = \a. phase a=0 /\ owner a IN keep` >>
  qabbrev_tac `P = \a. if isRet a then r(pc(owner a)) else vp (owner a) (phase a MOD 4)` >>
  qabbrev_tac `J = \a. if isRet a then height(owner a) else vh (owner a) (phase a MOD 4)` >>
  qabbrev_tac `N = \a. isRet a /\ need(owner a)` >>
  qabbrev_tac `raw = \a. if isRet a then tag(owner a) else vraw (owner a) (phase a MOD 4)` >>
  qabbrev_tac `B = \a. if isRet a then boolean(owner a) else vb (owner a) (phase a MOD 4)` >>
  qabbrev_tac `A = {a | a IN family /\ Reach E root a}` >>
  `!u. u IN keep ==>
    P (copy 0 u)=r(pc u) /\ J (copy 0 u)=height u /\ N (copy 0 u)=need u /\
    raw (copy 0 u)=tag u /\ B (copy 0 u)=boolean u` by
    simp[Abbr `P`, Abbr `J`, Abbr `N`, Abbr `raw`, Abbr `B`, Abbr `isRet`] >>
  `!u i. Visit i u ==>
    P (copy i u)=vp u (i MOD 4) /\ J (copy i u)=vh u (i MOD 4) /\
    ~N (copy i u) /\ raw (copy i u)=vraw u (i MOD 4) /\ B (copy i u)=vb u (i MOD 4)` by
    (rpt gen_tac >> disch_tac >> `i<8 /\ ~(i=0 /\ u IN keep)` by
       (fs[Abbr `Visit`, Abbr `D`, Abbr `keep`] >> decide_tac) >>
     simp[Abbr `P`, Abbr `J`, Abbr `N`, Abbr `raw`, Abbr `B`, Abbr `isRet`]) >>
  `root IN family /\ P root=(if late then r(pc z) else r(pc e)) /\
    J root=(if initial \/ pc e=b+3 then height e-1 else height e) /\
    N root=(if late then need z else if e IN keep then need e else F) /\
    (!k l i. raw root k=SOME(l,i) ==> (initial ==> k<>0) /\
             tag e (if initial \/ pc e=b+3 then k+1 else k)=SOME(l,i)) /\
    (!k. B root k ==> (initial ==> k<>0) /\ boolean e (if initial \/ pc e=b+3 then k+1 else k))` by
    suspend "root" >>
  `!a y k l. E a y /\ raw y k=SOME(l,b) ==> ?j. raw a j=SOME(l,b)` by
    suspend "predecessor" >>
  `FINITE A /\ root IN A /\
    (!a y. a IN A /\ E a y ==> y IN A /\ R y<R a) /\
    (!a k l. a IN A /\ raw a k=SOME(l,b) ==> ?j. raw root j=SOME(l,b))` by
    suspend "restrict" >>
  qexistsl [`family`,`A`,`root`,`R`,`P`,`J`,`N`,`raw`,`B`,`E`] >>
  CONV_TAC (HO_REWR_CONV UNWIND_FORALL_THM2) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[Abbr `A`, Abbr `Reach`] >>
  simp[markerTheory.Abbrev_def, SF CONJ_ss] >>
  suspend "rows"
QED

Resume conditional_jump_port_table[root]:
  ASM_CASES_TAC ``initial:bool``
  >- (`pc e=b+1` by
        (qpat_assum `Abbrev (initial = _)` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >> simp[]) >>
      `~late /\ e NOTIN keep` by simp[Abbr `late`, Abbr `keep`] >>
      `Visit 4 e` by simp[Abbr `Visit`] >>
      `copy 4 e IN family` by simp[] >>
      qpat_assum `!u. u IN D \/ (initial /\ u=e) ==> _`
        (qspec_then `e` mp_tac) >>
      simp[Abbr `root`, Abbr `r`, splice_pc_def, Abbr `vp`, Abbr `vh`,
           Abbr `H`, Abbr `vraw`, Abbr `vb`] >>
      strip_tac >> conj_tac
      >- (rpt gen_tac >> Cases_on `k=0` >> simp[] >> strip_tac >>
          `(k-1)+2=k+1` by (qpat_assum `k<>0` mp_tac >> decide_tac) >>
          gvs[Abbr `U`, CaseEq "option"] >> metis_tac[]) >>
      rpt strip_tac >> `(k-1)+2=k+1` by (qpat_assum `k<>0` mp_tac >> decide_tac) >> metis_tac[])
  >- (ASM_CASES_TAC ``late:bool``
      >- (qpat_assum `late ==> _` mp_tac >> simp[] >> strip_tac >>
          `copy 0 z IN family` by simp[] >> simp[Abbr `root`]) >>
      `pc e <> b+2 /\ pc e <> b+3` by
        (qpat_assum `~late` mp_tac >>
         qpat_assum `Abbrev (late = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >> simp[]) >>
      Cases_on `e IN keep`
      >- (`copy 0 e IN family` by simp[] >> simp[Abbr `root`]) >>
      `pc e <> b+1` by
        (qpat_assum `~initial` mp_tac >>
         qpat_assum `Abbrev (initial = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >> simp[]) >>
      `~(pc e < b) /\ ~(b + 4 <= pc e)` by
        (qpat_x_assum `~(e IN keep)` mp_tac >> simp[Abbr `keep`]) >>
      `pc e=b` by
        (map_every (fn pat => qpat_assum pat mp_tac)
           [`pc e <> b+1`,`pc e <> b+2`,`pc e <> b+3`, `~(pc e < b)`, `~(b+4 <= pc e)`] >>
         decide_tac) >>
      `e IN D` by simp[Abbr `D`] >>
      `Visit 0 e` by simp[Abbr `Visit`] >>
      `copy 0 e IN family` by simp[] >>
      qpat_assum `!u. u IN D \/ (initial /\ u=e) ==> _`
        (qspec_then `e` mp_tac) >>
      simp[Abbr `root`, Abbr `r`, splice_pc_def, Abbr `vp`, Abbr `vh`,
           Abbr `H`, Abbr `vraw`, Abbr `vb`] >>
      strip_tac >> conj_tac
      >- (rpt gen_tac >> Cases_on `k=0` >> simp[] >> strip_tac >>
          `(k-1)+1=k` by (qpat_assum `k<>0` mp_tac >> decide_tac) >>
          gvs[Abbr `U`, CaseEq "option"] >> metis_tac[]) >>
      rpt strip_tac >> `(k-1)+1=k` by (qpat_assum `k<>0` mp_tac >> decide_tac) >> metis_tac[])
QED

Resume conditional_jump_port_table[predecessor]:
  `!u. u IN D ==> ~(initial /\ u=e)` by
    (simp[Abbr `D`,Abbr `initial`] >> decide_tac) >>
  `!u. u IN D \/ (initial /\ u=e) ==>
     z0 u IN keep /\ z1 u IN keep /\
     (!k t s. tag (z0 u) k=SOME t /\ tag (z1 u) k=SOME s ==> t=s) /\
     (u IN D ==> !k t. (tag (z0 u) k=SOME t \/ tag (z1 u) k=SOME t) ==>
                                      tag u (k+1)=SOME t)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!u. u IN D \/ (initial /\ u=e) ==> _`
       (qspec_then `u` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     disch_tac >>
     qpat_assum `!w. w IN D ==> ~(initial /\ w=e)` (drule_then (fn guard =>
       qpat_assum `!k t. _ ==> tag u (if _ then _ else _) = SOME t`
         (ACCEPT_TAC o REWRITE_RULE[guard])))) >>
  `!a. raw a = (if phase a=0 /\ owner a IN keep then tag (owner a) else
    \k. if phase a MOD 4 < 2 then
          (if k=0 then NONE else U (owner a) (k-1))
        else if phase a MOD 4=2 then
          (if k=0 then SOME(x,b+2) else if k=1 then NONE else U (owner a) (k-2))
        else tag (z1 (owner a)) k)` by
    (gen_tac >> `phase a MOD 4 < 4` by simp[arithmeticTheory.MOD_LESS] >>
     `phase a MOD 4 <> 4` by
       (qpat_assum `phase a MOD 4 < 4` mp_tac >> decide_tac) >>
     simp[Abbr `raw`,Abbr `isRet`,Abbr `vraw`]) >>
  qspecl_then [`keep`,`D`,`e`,`initial`,`z0`,`z1`,`old`,`copy`,`owner`,
    `phase`,`family`,`E`,`tag`,`b`,`x`,`Visit`]
    mp_tac port_table_raw_predecessor >>
  (impl_tac >- simp[Abbr `Visit`]) >>
  disch_then (mp_tac o CONV_RULE (TOP_DEPTH_CONV
    (FIRST_CONV [HO_REWR_CONV UNWIND_FORALL_THM2, BETA_CONV]))) >>
  impl_tac
  >- (ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- (rpt gen_tac >> disch_tac >>
        qpat_assum `!a y. E a y ==> a IN family /\ y IN family /\ R y < R a`
          (qspecl_then [`a`,`y`] mp_tac) >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  simp[Abbr `U`]
QED

Resume conditional_jump_port_table[restrict]:
  qspecl_then [`family`,`E`,`root`,`R`,`raw`,`b`]
    (mp_tac o CONV_RULE (TOP_DEPTH_CONV
      (FIRST_CONV [HO_REWR_CONV UNWIND_FORALL_THM2, BETA_CONV]))) port_reachable_restriction >>
  rewrite_tac[LET_THM] >> BETA_TAC >> impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  simp[Abbr `A`, Abbr `Reach`] >> strip_tac >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume conditional_jump_port_table[rows]:
  conj_tac >- (gvs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disch_then (mk_asm "rootProducer") >>
  qabbrev_tac `relocate = \l i. if i=b then (@j. Producer q l j)
                     else if i=b+2 then b+1 else r i` >>
  `!l i. (i<b \/ b+4<=i) ==> relocate l i = r i` by
    (rpt gen_tac >> strip_tac >> simp[Abbr `relocate`] >> decide_tac) >>
  `!l. relocate l (b+2) = b+1` by simp[Abbr `relocate`] >>
  `!a k l i. a IN A /\ raw a k = SOME(l,i) /\ Producer p l i ==>
       Producer q l (relocate l i)` by
    (rpt gen_tac >> strip_tac >>
     Cases_on `i=b`
     >- (`?j. raw root j = SOME(l,b)` by
           (qpat_assum `!a k l. a IN A /\ raw a k = SOME(l,b) ==> _`
              (qspecl_then [`a`,`k`,`l`] mp_tac) >> simp[]) >>
         rename1 `raw root j = SOME(l,b)` >>
         asm "rootProducer" (qspecl_then [`j`,`l`] mp_tac) >>
         simp[Abbr `relocate`] >> disch_then (ACCEPT_TAC o SELECT_RULE)) >>
     qpat_assum `!l i. Producer p l i ==> _`
       (qspecl_then [`l`,`i`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (DISJ_CASES_THEN2 (CONJUNCTS_THEN assume_tac)
       (DISJ_CASES_THEN2 (CONJUNCTS_THEN assume_tac) assume_tac))
     >- (`relocate l i = r i` by
           (qpat_assum `!l i. (i<b \/ b+4<=i) ==> _`
              (qspecl_then [`l`,`i`] mp_tac) >> simp[]) >> simp[])
     >- (qpat_x_assum `i = b + 2` SUBST_ALL_TAC >>
         qpat_x_assum `l = x` SUBST_ALL_TAC >>
         `?d. C p x d` by metis_tac[Abbr `Producer`] >>
         rename1 `C p x d` >>
         `C q x (r d)` by simp[] >>
         `b+1<LENGTH q` by
           (qpat_assum `b+3<LENGTH q` mp_tac >> decide_tac) >>
         simp[Abbr `Producer`] >> metis_tac[]) >>
     qpat_assum `i <> b` mp_tac >>
     qpat_assum `i = b` (rewrite_tac o single)) >>
  `!u k l i. u IN keep /\ copy 0 u IN A /\ tag u k = SOME(l,i) ==>
       Producer q l (relocate l i)` by
    (rpt gen_tac >> strip_tac >>
     `u IN V` by fs[Abbr `keep`] >>
     `Slots p (height u) (need u) (tag u) (boolean u)` by metis_tac[] >>
     `Producer p l i` by metis_tac[Abbr `Slots`] >>
     `raw (copy 0 u) k = SOME(l,i)` by simp[] >>
     metis_tac[]) >>
  `!u i. copy i u IN A /\ Visit i u ==>
     copy 0 (z0 u) IN A /\ copy 0 (z1 u) IN A` by
    (qspecl_then [`D`,`e`,`initial`,`keep`,`copy`,`owner`,`phase`,`family`,
      `E`,`root`,`A`,`z0`,`z1`,`Visit`]
      mp_tac port_visit_exits_reached >>
     (impl_tac >- simp[Abbr `Visit`]) >>
     disch_then (mp_tac o CONV_RULE (TOP_DEPTH_CONV
       (FIRST_CONV [HO_REWR_CONV UNWIND_FORALL_THM2, BETA_CONV]))) >>
     impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- (rpt strip_tac >>
           qpat_assum `!u y. u IN keep ==> (E (copy 0 u) y <=> _)`
             (qspecl_then [`u`,`y`] mp_tac) >> simp[] >> metis_tac[]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- simp[SUBSET_DEF, Abbr `A`] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac
         >- (Cases_on `initial` >- (qexistsl [`4`,`e`] >> simp[Abbr `root`]) >>
             Cases_on `late` >- (qexistsl [`0`,`z`] >> simp[Abbr `root`]) >>
             qexistsl [`0`,`e`] >> simp[Abbr `root`]) >>
         conj_tac >- simp[Abbr `A`,Abbr `Reach`] >>
         rpt gen_tac >> strip_tac >>
         qpat_assum `!a y. a IN A /\ E a y ==> y IN A /\ R y < R a`
           (qspecl_then [`a`,`y`] mp_tac) >> simp[]) >>
     disch_then (fn th => rpt gen_tac >> strip_tac >>
       qspec_then `copy i u` mp_tac th) >>
     `i<8` by (qpat_assum `Visit i u` mp_tac >>
       simp[NoAsms, Abbr `Visit`] >> metis_tac[DECIDE ``!i:num. i<4 ==> i<8``]) >>
     simp[]) >>
  `!v. v IN keep \/ v IN D ==>
     P (copy 0 v)=r(pc v) /\ J (copy 0 v)=height v /\
     raw (copy 0 v)=rt v /\ B (copy 0 v)=rb v` by
    (gen_tac >> strip_tac
     >- simp[Abbr `rt`, Abbr `rb`] >>
     `pc v=b /\ v NOTIN keep /\ ~(initial /\ v=e)` by
       (qpat_assum `v IN D` mp_tac >>
        simp[NoAsms, Abbr `D`, Abbr `keep`, Abbr `initial`] >>
        rpt disch_tac >> CCONTR_TAC >> gvs[]) >>
     `Visit 0 v` by simp[Abbr `Visit`] >>
     simp[Abbr `rt`, Abbr `rb`, Abbr `vp`, Abbr `vh`, Abbr `H`, Abbr `r`, splice_pc_def]) >>
  `!u j. j=4 \/ j=5 ==>
     vp u j=r(pc(if j=4 then z0 u else z1 u)) /\
     vraw u j=tag(if j=4 then z0 u else z1 u) /\
     vb u j=boolean(if j=4 then z0 u else z1 u)` by
    (rpt strip_tac >> simp[FUN_EQ_THM, Abbr `vp`, Abbr `vraw`, Abbr `vb`]) >>
  `!h d n tg bl. Slots q h n tg bl ==> ?t. Shape q h d n tg bl t` by
    (rpt gen_tac >> strip_tac >>
     qexists `(ARB:asm_state) with <| as_pc := d; as_stack := GENLIST
       (\k. case tg k of NONE => 0w | SOME(l,i) => n2w (THE (FLOOKUP
         (SND(compute_label_offsets q)) l))) h; as_call_ctx := cc; as_requests := req |>` >>
     simp[Abbr `Shape`] >>
     qpat_assum `Slots q h n tg bl` mp_tac >>
     simp[NoAsms, Abbr `Slots`] >> strip_tac >> simp[] >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!k l i. tg k=SOME(l,i) ==> _` (qspecl_then [`k`,`l`,`i`] mp_tac) >>
     simp[Abbr `Producer`, Abbr `C`] >> strip_tac >> simp[] >>
     rename [`FLOOKUP _ l=SOME off`,`FLOOKUP _ off=SOME dst`] >>
     qexistsl [`off`,`dst`] >> simp[]) >>
  `!i h tg e1 p1 h1 e2 p2 h2.
      (!v. e1 v ==> ?w. e2 w /\ p2 w=p1 v /\ h2 w=h1 v) /\
      (!w. e2 w ==> ?v. e1 v /\ p1 v=p2 w /\ h1 v=h2 w) ==>
      (Row q i h tg e1 p1 h1 <=> Row q i h tg e2 p2 h2)` by
    ((qpat_x_assum `Abbrev (Row = _)` mp_tac >> POP_ASSUM_LIST kall_tac >>
     strip_tac >> rpt gen_tac >> strip_tac >>
     `(\f n. ?v. e1 v /\ f (p1 v) /\ h1 v=n) =
      (\f n. ?w. e2 w /\ f (p2 w) /\ h2 w=n)` by
       (simp[FUN_EQ_THM] >> metis_tac[]) >>
     `(\f n. !v. e1 v ==> f (p1 v) /\ h1 v=n) =
      (\f n. !w. e2 w ==> f (p2 w) /\ h2 w=n)` by
       (simp[FUN_EQ_THM] >> metis_tac[]) >>
     `(!v. ~e1 v) <=> (!w. ~e2 w)` by metis_tac[] >>
     SIMP_TAC bool_ss [Abbr `Row`] >>
     qpat_assum `(\f n. ?v. e1 v /\ f (p1 v) /\ h1 v=n) = _`
       (pure_rewrite_tac o single) >>
     qpat_assum `(\f n. !v. e1 v ==> f (p1 v) /\ h1 v=n) = _`
       (pure_rewrite_tac o single) >>
     qpat_assum `(!v. ~e1 v) <=> _` (rewrite_tac o single) >> (gvs[FUN_EQ_THM]))) >>
  `!a a' y y' p1 h1 t1 b1 p2 h2 t2 b2.
      p1 a=p2 a' /\ h1 a=h2 a' /\ h1 y=h2 y' /\
      t1 a=t2 a' /\ t1 y=t2 y' /\ b1 a=b2 a' /\ b1 y=b2 y' ==>
      (Flow q p1 h1 t1 b1 a y <=> Flow q p2 h2 t2 b2 a' y')` by
    (qpat_x_assum `Abbrev (Flow = _)` mp_tac >> POP_ASSUM_LIST kall_tac >>
     strip_tac >> rpt gen_tac >> strip_tac >> simp[Abbr `Flow`]) >>
  `!h n tg bl rho. Slots p h n tg bl /\
     (!k l i. tg k = SOME(l,i) ==> Producer q l (rho l i)) ==>
     Slots q h n (Tr rho tg) bl` by
    (qpat_x_assum `Abbrev (Slots = _)` mp_tac >>
     qpat_x_assum `Abbrev (Tr = _)` mp_tac >> POP_ASSUM_LIST kall_tac >>
     ntac 2 disch_tac >>
     `!rho tg k. (Tr rho tg k = NONE <=> tg k = NONE)` by
       (rpt gen_tac >> Cases_on `tg k` >> simp[Abbr `Tr`]) >>
     `!rho tg k l j. (Tr rho tg k = SOME(l,j) <=>
          ?i. tg k = SOME(l,i) /\ j = rho l i)` by
       (rpt gen_tac >> Cases_on `tg k` >> simp[Abbr `Tr`] >>
        rename1 `tg k = SOME t` >> PairCases_on `t` >> simp[] >> metis_tac[]) >>
     simp[Abbr `Slots`] >> metis_tac[]) >>
  qabbrev_tac `tgR = \a. Tr relocate (raw a)` >>
  `!u. u IN keep /\ copy 0 u IN A ==>
     Slots q (J (copy 0 u)) (N (copy 0 u)) (tgR (copy 0 u)) (B (copy 0 u))` by
    (gen_tac >> strip_tac >>
     `u IN V` by fs[Abbr `keep`] >>
     `Slots p (height u) (need u) (tag u) (boolean u)` by metis_tac[] >>
     `rt u = tag u /\ rb u = boolean u` by simp[Abbr `rt`, Abbr `rb`] >>
     simp[Abbr `tgR`] >>
     qpat_assum `!h n tg bl rho. _ ==> Slots q h n (Tr rho tg) bl` irule >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!u k l i. u IN keep /\ copy 0 u IN A /\ tag u k = _ ==> _`
       irule >> qexistsl [`k`,`u`] >> simp[]) >>
  `!u. u IN keep ==>
     P (copy 0 u)<LENGTH q /\ Row q (P (copy 0 u)) (J (copy 0 u))
       (tgR (copy 0 u)) (E (copy 0 u)) P J /\
     (!y. E (copy 0 u) y ==>
       Legal q (P (copy 0 u)) (tgR (copy 0 u)) (P y) /\
       Flow q P J tgR B (copy 0 u) y)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!u rho. u IN keep /\ _ ==> _`
       (qspecl_then [`u`,`relocate`] mp_tac) >>
     (impl_tac >-
       (simp[] >> gen_tac >> disch_tac >>
        qpat_assum `!l i. (i<b \/ b+4<=i) ==> _` irule >> fs[Abbr `keep`])) >>
     strip_tac >>
     `!v. old u v ==> (v IN keep \/ v IN D) /\ rank v < rank u` by
       (qpat_assum `!u v. u IN keep /\ old u v ==> _`
          (qspec_then `u` mp_tac) >> simp[]) >>
     `!v. old u v ==> E (copy 0 u) (copy 0 v) /\
        P (copy 0 v)=(r o pc) v /\ J (copy 0 v)=height v` by
       (gen_tac >> disch_tac >>
        `v IN keep \/ v IN D` by
          (qpat_assum `!v. old u v ==> _` (drule_then strip_assume_tac) >> simp[]) >>
        simp[] >> qexists `v` >> simp[]) >>
     `rt u = tag u` by simp[Abbr `rt`] >>
     `tgR (copy 0 u) = Tr relocate (tag u)` by simp[Abbr `tgR`] >>
     simp[] >> conj_tac
     >- (`(!v. old u v ==> ?y. E (copy 0 u) y /\ P y=(r o pc) v /\ J y=height v) /\
          (!y. E (copy 0 u) y ==> ?v. old u v /\ (r o pc) v=P y /\ height v=J y)` by
           (conj_tac
            >- (rpt strip_tac >> qexists `copy 0 v` >>
                qpat_assum `!v. old u v ==> E (copy 0 u) (copy 0 v) /\ _`
                  (drule_then ACCEPT_TAC)) >>
            gen_tac >> disch_tac >>
            `?v. old u v /\ y=copy 0 v` by
              (qpat_assum `!u y. u IN keep ==> (E (copy 0 u) y <=> _)`
                (qspecl_then [`u`,`y`] mp_tac) >> simp[]) >>
            qpat_assum `!v. old u v ==> E (copy 0 u) (copy 0 v) /\ _`
              (drule_then strip_assume_tac) >>
            qexists `v` >> simp[]) >>
         qpat_assum `!i h tg e1 p1 h1 e2 p2 h2. _ ==> (Row _ _ _ _ _ _ _ <=> _)`
           (drule_then (irule o iffLR)) >> simp[]) >>
     qx_gen_tac `y` >> disch_tac >>
     `?v. old u v /\ y=copy 0 v` by
       (qpat_assum `!u y. u IN keep ==> (E (copy 0 u) y <=> _)`
         (qspecl_then [`u`,`y`] mp_tac) >> simp[]) >>
     qpat_x_assum `y = copy 0 v` SUBST_ALL_TAC >>
     `rank v < rank u` by
       (qpat_assum `!v. old u v ==> _ /\ rank v < rank u`
          (qspec_then `v` mp_tac) >> simp[]) >>
     `v<>u` by (qpat_assum `rank v < rank u` mp_tac >>
       POP_ASSUM_LIST kall_tac >> disch_tac >> disch_then SUBST_ALL_TAC >> fs[]) >>
     qpat_assum `!v. old u v ==> Legal _ _ _ _ /\ Flow _ _ _ _ _ _ _`
       (qspec_then `v` (drule_then strip_assume_tac)) >>
     simp[] >>
     qpat_assum `!a a' y y' p1 h1 t1 b1 p2 h2 t2 b2. _ ==> (Flow _ _ _ _ _ _ _ <=> _)`
       (qspecl_then [`u`,`copy 0 u`,`v`,`copy 0 v`,`r o pc`,`height`,
         `\w. if w=u then Tr relocate (tag u) else Tr relocate (rt w)`,
         `\w. if w=u then boolean u else rb w`,`P`,`J`,`tgR`,`B`]
         mp_tac) >>
     (impl_tac >-
       ((Q.SUBGOAL_THEN `v IN keep \/ v IN D` ASSUME_TAC >-
         (qpat_assum `!v. old u v ==> _ /\ rank v < rank u`
            (qspec_then `v` mp_tac) >> simp[])) >>
        qpat_assum `!v. v IN keep \/ v IN D ==> P (copy 0 v) = _ /\ _`
          (qspec_then `v` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
        `B (copy 0 u) = boolean u` by simp[Abbr `rb`] >>
        simp[Abbr `tgR`])) >>
     disch_then (irule o iffLR) >>
     simp[NoAsms, Abbr `rt`, Abbr `rb`, Abbr `Tr`] >>
     qpat_assum `Flow q (r o pc) height _ _ u v`
       (mp_tac o SIMP_RULE (srw_ss()) [Abbr `rt`, Abbr `rb`, Abbr `Tr`]) >> simp[]) >>
  `!u i. Visit i u ==>
     tgR (copy i u) = (\k. if i MOD 4=2 /\ k=0 then SOME(x,b+1)
                         else Tr relocate (vraw u (i MOD 4)) k)` by
    (rpt gen_tac >> disch_tac >> simp[FUN_EQ_THM, Abbr `tgR`] >>
     rpt gen_tac >> Cases_on `i MOD 4=2 /\ k=0` >> simp[Abbr `Tr`, Abbr `vraw`]) >>
  `!u i. copy i u IN A /\ Visit i u ==>
     Slots q (J (copy i u)) (N (copy i u)) (tgR (copy i u)) (B (copy i u)) /\
     P (copy i u)<LENGTH q /\ Row q (P (copy i u)) (J (copy i u))
       (tgR (copy i u)) (E (copy i u)) P J /\
     (!y. E (copy i u) y ==>
       Legal q (P (copy i u)) (tgR (copy i u)) (P y) /\
       Flow q P J tgR B (copy i u) y)` by
    (rpt gen_tac >> strip_tac >>
     (Q.SUBGOAL_THEN `u IN D \/ (initial /\ u=e)` ASSUME_TAC >- fs[Abbr `Visit`]) >>
     `copy 0 (z0 u) IN A /\ copy 0 (z1 u) IN A` by
       (qpat_assum `!u i. copy i u IN A /\ Visit i u ==> _`
         (qspecl_then [`u`,`i`] mp_tac) >> simp[]) >>
     qpat_assum `!u. u IN D \/ (initial /\ u=e) ==> _`
       (qspec_then `u` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `C q x (r (pc (z0 u))) /\
      (!v k l i. (v=z0 u \/ v=z1 u) /\ tag v k=SOME(l,i) ==>
                 Producer q l (relocate l i))` by
       (conj_tac >- simp[] >> rpt strip_tac >>
        qpat_x_assum `v = _` SUBST_ALL_TAC >>
        qpat_assum `!u k l i. u IN keep /\ copy 0 u IN A /\ tag u k = _ ==> _`
          irule >> goal_assum (drule_at Any) >> simp[]) >>
     qabbrev_tac `m = i MOD 4` >>
     `m<4` by simp[Abbr `m`, arithmeticTheory.MOD_LESS] >>
     qabbrev_tac `lp = \v:num#num. vp u (FST v)` >>
     qabbrev_tac `lh = \v:num#num. vh u (FST v)` >>
     qabbrev_tac `lt = \(v:num#num) k. if FST v=2 /\ k=0 then SOME(x,b+1)
                                else Tr relocate (vraw u (FST v)) k` >>
     qabbrev_tac `lb = \v:num#num. vb u (FST v)` >>
     qpat_assum `!rho P J T B. _ ==> _`
       (qspecl_then [`relocate`,`lp`,`lh`,`lt`,`lb`] mp_tac) >>
     (impl_tac >- simp[NoAsms, Abbr `lp`, Abbr `lh`, Abbr `lt`, Abbr `lb`]) >>
     disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
     qabbrev_tac `dst = \j:num. if j=4 then copy 0 (z0 u) else
                                if j=5 then copy 0 (z1 u) else copy (i+1) u` >>
     `!y. E (copy i u) y <=> ?j. VE m j /\ y=dst j` by
       (gen_tac >> qpat_assum `!i u y. Visit i u ==> (E (copy i u) y <=> _)`
          (qspecl_then [`i`,`u`,`y`] mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >> disch_then SUBST1_TAC >>
        qpat_assum `Abbrev (m = _)` (pure_rewrite_tac o single o GSYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
        `m=0 \/ m=1 \/ m=2 \/ m=3` by decide_tac >>
        qpat_assum `m = _` (fn th => simp[NoAsms, th, Abbr `VE`, Abbr `dst`,
               LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM])) >>
     `!j. VE m j ==> P (dst j)=lp (j,0) /\ J (dst j)=lh (j,0) /\
         tgR (dst j)=lt (j,0) /\ B (dst j)=lb (j,0)` by
       (gen_tac >> disch_tac >>
        qpat_assum `VE m j` mp_tac >> simp[NoAsms, Abbr `VE`] >> strip_tac
        >- (`Visit (i+1) u /\ (i+1) MOD 4=j` by
              (qpat_assum `Visit i u` mp_tac >> qpat_assum `j=m+1` mp_tac >>
               qpat_assum `m<3` mp_tac >>
               qpat_assum `Abbrev (Visit = _)` mp_tac >>
               qpat_assum `Abbrev (m = _)` mp_tac >> POP_ASSUM_LIST kall_tac >>
               ntac 2 disch_tac >>
               simp[NoAsms, Abbr `Visit`, Abbr `m`] >>
               rpt disch_tac >>
               `i<8` by (pop_assum mp_tac >> strip_tac >> decide_tac) >>
               `i=0 \/ i=1 \/ i=2 \/ i=3 \/ i=4 \/ i=5 \/ i=6 \/ i=7` by decide_tac >>
               qpat_assum `i = _` (fn th => fs[th])) >>
            `j<>4 /\ j<>5` by decide_tac >>
            simp[Abbr `dst`, Abbr `lp`, Abbr `lh`, Abbr `lt`, Abbr `lb`]) >>
        qpat_assum `j = _` SUBST1_TAC >>
        simp[Abbr `dst`, Abbr `lp`, Abbr `lh`, Abbr `lt`, Abbr `lb`,
             Abbr `vh`, Abbr `tgR`, Abbr `rt`, Abbr `rb`, FUN_EQ_THM]) >>
     `P (copy i u)=lp (m,0) /\ J (copy i u)=lh (m,0) /\
      tgR (copy i u)=lt (m,0) /\ B (copy i u)=lb (m,0) /\ N (copy i u)=vn u m` by
       (simp[Abbr `lp`, Abbr `lh`, Abbr `lt`, Abbr `lb`, Abbr `m`, Abbr `vn`,
             arithmeticTheory.MOD_LESS, FUN_EQ_THM] >> decide_tac) >>
     `Slots q (vh u m) (vn u m) (lt (m,0)) (lb (m,0))` by
       (`m <> 4 /\ m <> 5` by decide_tac >>
        qpat_assum `!i. i<4 ==> Slots q _ _ _ _` (drule_then mp_tac) >>
        map_every (fn p => qpat_assum p mp_tac) [`m <> 4`,`m <> 5`] >>
        csimp[NoAsms, Abbr `vn`]) >>
     `vp u m < LENGTH q /\ Row q (vp u m) (vh u m) (lt (m,0))
       (\v. VE m (FST v)) lp lh` by
       (qpat_assum `!i. i<4 ==> vp u i < LENGTH q /\ _` (qspec_then `m` mp_tac) >> simp[]) >>
     `lp (m,0) = vp u m /\ lh (m,0) = vh u m` by simp[Abbr `lp`, Abbr `lh`] >>
     conj_tac >- simp[] >>
     conj_tac >- simp[] >>
     conj_tac
     >- (simp[] >>
         `(!v:num#num. VE m (FST v) ==> ?y. E (copy i u) y /\ P y=lp v /\ J y=lh v) /\
          (!y. E (copy i u) y ==> ?v:num#num. VE m (FST v) /\ lp v=P y /\ lh v=J y)` by
           (conj_tac
            >- (rpt strip_tac >> qexists `dst (FST v)` >> conj_tac
                >- (simp[] >> qexists `FST v` >> simp[]) >>
                qpat_assum `!j. VE m j ==> P (dst j) = _ /\ _`
                  (drule_then strip_assume_tac) >> simp[Abbr `lp`, Abbr `lh`]) >>
            gen_tac >> disch_tac >>
            `?j. VE m j /\ y=dst j` by
              (qpat_assum `!y. E (copy i u) y <=> _`
                 (drule_then ACCEPT_TAC o iffLR)) >>
            qpat_x_assum `y=dst j` SUBST_ALL_TAC >>
            qpat_assum `!j. VE m j ==> P (dst j) = _ /\ _`
              (drule_then strip_assume_tac) >> qexists `(j,0)` >> simp[]) >>
         qpat_assum `!i h tg e1 p1 h1 e2 p2 h2. _ ==> (Row _ _ _ _ _ _ _ <=> _)`
           (qspecl_then [`vp u m`,`vh u m`,`lt (m,0)`,`\v. VE m (FST v)`,
             `lp`,`lh`,`E (copy i u)`,`P`,`J`] mp_tac) >>
         BETA_TAC >> (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then (irule o iffLR) >> first_assum ACCEPT_TAC) >>
     qx_gen_tac `y` >> disch_tac >>
     `?j. VE m j /\ y=dst j` by
              (qpat_assum `!y. E (copy i u) y <=> _`
                 (drule_then ACCEPT_TAC o iffLR)) >>
     qpat_x_assum `y=dst j` SUBST_ALL_TAC >>
     qpat_assum `!j. VE m j ==> P (dst j) = _ /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac
     >- (`Legal q (vp u m) (lt (m,0)) (vp u j)` by
           (qpat_assum `!i j. VE i j ==> Legal _ _ _ _` (drule_then ACCEPT_TAC)) >>
         simp[Abbr `lp`]) >>
     qpat_assum `!a a' y y' p1 h1 t1 b1 p2 h2 t2 b2. _ ==> (Flow _ _ _ _ _ _ _ <=> _)`
       (qspecl_then [`(m,0)`,`copy i u`,`(j,0)`,`dst j`,`lp`,`lh`,`lt`,`lb`,`P`,`J`,`tgR`,`B`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (irule o iffLR) >>
     qpat_assum `!i j. VE i j ==> Flow _ _ _ _ _ _ _` (drule_then ACCEPT_TAC)) >>
  `!a. a IN A ==> Slots q (J a) (N a) (tgR a) (B a) /\
     P a<LENGTH q /\ Row q (P a) (J a) (tgR a) (E a) P J /\
     (!y. E a y ==> Legal q (P a) (tgR a) (P y) /\ Flow q P J tgR B a y)` by
    (gen_tac >> disch_tac >>
     `a IN family` by (qpat_assum `a IN A` mp_tac >> simp[NoAsms, Abbr `A`]) >>
     `?i u. a=copy i u /\ (i=0 /\ u IN keep \/ Visit i u)` by
       (qexistsl [`phase a`,`owner a`] >>
        qpat_assum `!a. a IN family ==> _ /\ _ /\ _` (drule_then strip_assume_tac) >>
        simp[]) >>
     qpat_x_assum `a = copy i u` SUBST_ALL_TAC
     >- (qpat_x_assum `i=0` SUBST_ALL_TAC >>
         conj_tac
         >- (qpat_assum `!u. u IN keep /\ copy 0 u IN A ==> Slots q _ _ _ _`
               (drule_all_then ACCEPT_TAC)) >>
         qpat_assum `!u. u IN keep ==> _ /\ Row q _ _ _ _ _ _ /\ _`
           (drule_then ACCEPT_TAC)) >>
     qpat_assum `!u i. copy i u IN A /\ Visit i u ==> Slots q _ _ _ _ /\ _`
       (drule_all_then ACCEPT_TAC)) >>
  qsuff_tac `?T. T = (\a. Tr relocate (raw a)) /\
      (!a. a IN A ==> Slots q (J a) (N a) (T a) (B a) /\
         (?t. Shape q (J a) (P a) (N a) (T a) (B a) t) /\
         P a < LENGTH q /\ Row q (P a) (J a) (T a) (E a) P J) /\
      (!a y. a IN A /\ E a y ==> Legal q (P a) (T a) (P y) /\ Flow q P J T B a y)`
  >- (disch_then (qx_choose_then `tags` strip_assume_tac) >>
      qpat_x_assum `tags = _` SUBST_ALL_TAC >>
      qexists `relocate` >>
      conj_tac
      >- (gen_tac >> disch_tac >>
          qpat_assum `!a. a IN A ==> Slots q _ _ _ _ /\ _`
            (drule_then (strip_assume_tac o BETA_RULE)) >>
          SIMP_TAC bool_ss [SF ETA_ss] >>
          conj_tac >- first_assum ACCEPT_TAC >>
          reverse conj_tac >- simp[] >>
          goal_assum (drule_at Any)) >>
      qpat_assum `!a y. a IN A /\ E a y ==> Legal q _ _ _ /\ _` (mp_tac o BETA_RULE) >>
      SIMP_TAC bool_ss [SF ETA_ss]) >>
  qexists `tgR` >> (conj_tac >- simp[Abbr `tgR`]) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!a. a IN A ==> Slots q _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
      `?t. Shape q (J a) (P a) (N a) (tgR a) (B a) t` by
        (qpat_assum `!h d n tg bl. Slots q h n tg bl ==> _` irule >> first_assum ACCEPT_TAC) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexists `t` >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!a. a IN A ==> Slots q _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
  qpat_assum `!y. E a y ==> Legal _ _ _ _ /\ Flow _ _ _ _ _ _ _`
    (drule_then ACCEPT_TAC)
QED

Finalise conditional_jump_port_table
