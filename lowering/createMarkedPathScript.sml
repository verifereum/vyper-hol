(* Splitting caller paths without losing the marks of multi-event edges. *)
Theory createMarkedPath
Ancestors
  list pair relation

Definition create_marked_edge_def:
  create_marked_edge E (s,xs) (t,ys) <=> ?ms. E s ms t /\ ys = xs ++ ms
End

Theorem create_marked_rtc_rebase:
  !x y. RTC (create_marked_edge E) x y ==>
        !xs. ?ms. SND y = SND x ++ ms /\
                  RTC (create_marked_edge E) (FST x,xs) (FST y,xs ++ ms)
Proof
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >> simp[] >>
  map_every qx_gen_tac [`x`,`y`,`z`] >>
  map_every PairCases_on [`x`,`y`,`z`] >>
  simp[create_marked_edge_def, PULL_EXISTS] >> rpt strip_tac >>
  qpat_x_assum `!xs. ?ms. _` (qspec_then `xs` (qx_choose_then `left` strip_assume_tac)) >>
  rename1 `E y0 right z0` >> qexists_tac `left ++ right` >>
  simp[APPEND_ASSOC] >> irule (cj 2 RTC_RULES_RIGHT1) >>
  qexists_tac `(y0,xs ++ left)` >>
  simp[create_marked_edge_def, APPEND_ASSOC] >> metis_tac[]
QED

(* Stop at the first occurrence of Q. The front uses the smaller edge
   relation A, but the back still uses every edge of the supplied path. *)
Theorem create_marked_rtc_first_cut:
  !x y. RTC (create_marked_edge E) x y ==>
    !A Inv Q.
      (Q (FST y) \/ ~Inv (FST y)) /\
      (Q (FST x) \/ Inv (FST x)) /\
      (!u ms v. Inv u /\ ~Q u /\ E u ms v ==> A u ms v /\ (Q v \/ Inv v)) ==>
      ?z. Q (FST z) /\ RTC (create_marked_edge A) x z /\
          RTC (create_marked_edge E) z y
Proof
  ho_match_mp_tac RTC_STRONG_INDUCT >> conj_tac
  >- (rpt gen_tac >> Cases_on `Q (FST x)` >> simp[] >>
      strip_tac >> qexists_tac `x` >> simp[]) >>
  map_every qx_gen_tac [`x`,`y`,`z`] >>
  map_every PairCases_on [`x`,`y`,`z`] >>
  pure_rewrite_tac[create_marked_edge_def, FST, SND] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `ms` strip_assume_tac)
    (CONJUNCTS_THEN assume_tac)) >>
  map_every qx_gen_tac [`A`,`Inv`,`Q`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `y1 = x1 ++ ms` SUBST_ALL_TAC >>
  Cases_on `Q x0`
  >- (qexists_tac `(x0,x1)` >> simp[] >>
      irule (cj 2 RTC_RULES) >> qexists_tac `(y0,x1 ++ ms)` >>
      simp[create_marked_edge_def] >> metis_tac[]) >>
  `Inv x0` by metis_tac[] >>
  `A x0 ms y0 /\ (Q y0 \/ Inv y0)` by
    (qpat_assum `!u ms v. _ ==> A u ms v /\ _`
       (qspecl_then [`x0`,`ms`,`y0`] mp_tac) >> simp[]) >>
  qpat_x_assum `!A Inv Q. _` (qspecl_then [`A`,`Inv`,`Q`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qx_choose_then `cut` strip_assume_tac) >>
  qexists_tac `cut` >> simp[] >>
  irule (cj 2 RTC_RULES) >> qexists_tac `(y0,x1 ++ ms)` >>
  simp[create_marked_edge_def] >> metis_tac[]
QED
