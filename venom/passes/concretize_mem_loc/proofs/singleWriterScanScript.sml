(* Proof-only monotone coordinate scans, independent of BP and CFG. *)
Theory singleWriterScan
Ancestors list pred_set combin

Definition sw_out_def:
  sw_out (out,seed,preds) = out
End

Definition sw_rhs_def:
  sw_rhs (out,seed,preds) X = seed UNION BIGUNION (IMAGE X preds)
End

Definition sw_le_def:
  sw_le X Y <=> !v. X v SUBSET Y v
End

Definition sw_update_def:
  sw_update d X = \v. if v = sw_out d then sw_rhs d X else X v
End

Definition sw_consistent_def:
  sw_consistent ds <=> !d e. MEM d ds /\ MEM e ds /\
    sw_out d = sw_out e ==> d = e
End

Definition sw_admissible_def:
  sw_admissible ds X <=> !d. MEM d ds ==> X (sw_out d) SUBSET sw_rhs d X
End

Definition sw_scan_def:
  sw_scan [] X = X /\
  sw_scan (d::ds) X = sw_scan ds (sw_update d X)
End

Theorem sw_rhs_mono:
  sw_le X Y ==> sw_rhs d X SUBSET sw_rhs d Y
Proof
  Cases_on `d` >> Cases_on `r` >>
  rw[sw_le_def, sw_rhs_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem sw_update_lookup:
  sw_update d X v = if v = sw_out d then sw_rhs d X else X v
Proof
  simp[sw_update_def]
QED

Theorem sw_update_mono:
  sw_le X Y ==> sw_le (sw_update d X) (sw_update d Y)
Proof
  rw[sw_le_def, sw_update_def] >> metis_tac[sw_rhs_mono, sw_le_def]
QED

Theorem sw_update_grows:
  MEM d ds /\ sw_admissible ds X ==> sw_le X (sw_update d X)
Proof
  rw[sw_admissible_def, sw_le_def, sw_update_def] >>
  Cases_on `v = sw_out d` >> simp[]
QED

Theorem sw_update_admissible:
  sw_consistent ds /\ MEM d ds /\ sw_admissible ds X ==>
  sw_admissible ds (sw_update d X)
Proof
  rpt strip_tac >>
  `sw_le X (sw_update d X)` by metis_tac[sw_update_grows] >>
  rw[sw_admissible_def] >>
  Cases_on `sw_out d = sw_out d'`
  >- (`d = d'` by metis_tac[sw_consistent_def] >>
      gvs[sw_update_def] >> metis_tac[sw_rhs_mono]) >>
  `X (sw_out d') SUBSET sw_rhs d' X` by
    metis_tac[sw_admissible_def] >>
  `sw_rhs d' X SUBSET sw_rhs d' (sw_update d X)` by
    (irule sw_rhs_mono >> simp[]) >>
  `sw_update d X (sw_out d') = X (sw_out d')` by
    simp[sw_update_def] >>
  metis_tac[SUBSET_TRANS]
QED

Theorem sw_le_trans:
  sw_le X Y /\ sw_le Y Z ==> sw_le X Z
Proof
  rw[sw_le_def] >> metis_tac[SUBSET_TRANS]
QED

Theorem sw_scan_mono:
  !stream X Y. sw_le X Y ==> sw_le (sw_scan stream X) (sw_scan stream Y)
Proof
  Induct >> simp[sw_scan_def] >> metis_tac[sw_update_mono]
QED

Theorem sw_scan_admissible:
  !stream X. sw_consistent ds /\ EVERY (\d. MEM d ds) stream /\
    sw_admissible ds X ==> sw_admissible ds (sw_scan stream X)
Proof
  Induct >> simp[sw_scan_def] >> metis_tac[sw_update_admissible]
QED

Theorem sw_scan_grows:
  !stream X. sw_consistent ds /\ EVERY (\d. MEM d ds) stream /\
    sw_admissible ds X ==> sw_le X (sw_scan stream X)
Proof
  Induct >> simp[sw_scan_def, sw_le_def] >> rpt strip_tac >>
  `sw_admissible ds (sw_update h X)` by metis_tac[sw_update_admissible] >>
  `sw_le X (sw_update h X)` by metis_tac[sw_update_grows] >>
  `sw_le (sw_update h X) (sw_scan stream (sw_update h X))` by
    metis_tac[sw_le_def] >>
  metis_tac[sw_le_trans, sw_le_def]
QED

Theorem sw_bottom_admissible:
  sw_admissible ds (\v. {})
Proof
  simp[sw_admissible_def]
QED

Theorem sw_bottom_scan_admissible:
  sw_consistent ds /\ EVERY (\d. MEM d ds) stream ==>
  sw_admissible ds (sw_scan stream (\v. {}))
Proof
  metis_tac[sw_scan_admissible, sw_bottom_admissible]
QED

Theorem sw_bottom_prefix_grows:
  sw_consistent ds /\ EVERY (\d. MEM d ds) (xs ++ ys) ==>
  sw_le (sw_scan xs (\v. {})) (sw_scan ys (sw_scan xs (\v. {})))
Proof
  simp[EVERY_APPEND] >> rpt strip_tac >>
  irule sw_scan_grows >> metis_tac[sw_bottom_scan_admissible]
QED

(* Every visited writer installs at least its right-hand side at entry. *)
Theorem sw_scan_covers_rhs:
  !stream X d. sw_consistent ds /\ EVERY (\e. MEM e ds) stream /\
    sw_admissible ds X /\ MEM d stream ==>
    sw_rhs d X SUBSET sw_scan stream X (sw_out d)
Proof
  Induct >> simp[sw_scan_def] >> rpt strip_tac
  >- (`sw_admissible ds (sw_update d X)` by
        metis_tac[sw_update_admissible] >>
      `sw_le (sw_update d X) (sw_scan stream (sw_update d X))` by
        metis_tac[sw_scan_grows] >>
      fs[sw_le_def] >>
      first_x_assum (qspec_then `sw_out d` mp_tac) >>
      simp[sw_update_def]) >>
  `sw_le X (sw_update h X)` by metis_tac[sw_update_grows] >>
  `sw_admissible ds (sw_update h X)` by
    metis_tac[sw_update_admissible] >>
  `sw_rhs d (sw_update h X) SUBSET
     sw_scan stream (sw_update h X) (sw_out d)` by metis_tac[] >>
  metis_tac[sw_rhs_mono, SUBSET_TRANS]
QED

Definition sw_rounds_def:
  sw_rounds ds 0 = (\v. {}) /\
  sw_rounds ds (SUC n) = sw_scan ds (sw_rounds ds n)
End

Theorem sw_rounds_admissible:
  !n. sw_consistent ds ==> sw_admissible ds (sw_rounds ds n)
Proof
  Induct >> simp[sw_rounds_def, sw_bottom_admissible] >>
  strip_tac >> irule sw_scan_admissible >>
  simp[EVERY_MEM]
QED

Theorem sw_rounds_step:
  sw_consistent ds ==> sw_le (sw_rounds ds n) (sw_rounds ds (SUC n))
Proof
  strip_tac >> simp[sw_rounds_def] >> irule sw_scan_grows >>
  qexists_tac `ds` >> simp[EVERY_MEM, sw_rounds_admissible]
QED

Theorem sw_rounds_mono:
  !m n. sw_consistent ds /\ m <= n ==>
    sw_le (sw_rounds ds m) (sw_rounds ds n)
Proof
  Induct_on `n` >- simp[sw_le_def] >> rpt strip_tac >>
  Cases_on `m = SUC n` >- simp[sw_le_def] >>
  `m <= n` by decide_tac >>
  metis_tac[sw_le_trans, sw_rounds_step]
QED

Definition sw_seed_def:
  sw_seed ds a v <=> ?seed preds. MEM (v,seed,preds) ds /\ a IN seed
End

Definition sw_edge_def:
  sw_edge ds x y <=> ?seed preds. MEM (y,seed,preds) ds /\ x IN preds
End

Theorem sw_scan_member:
  sw_consistent ds /\ sw_admissible ds X /\ MEM (v,s,ps) ds /\
  (a IN s \/ ?x. x IN ps /\ a IN X x) ==>
  a IN sw_scan ds X v
Proof
  rpt strip_tac >>
  `sw_rhs (v,s,ps) X SUBSET sw_scan ds X (sw_out (v,s,ps))` by
    (irule sw_scan_covers_rhs >> simp[] >>
     qexists_tac `ds` >> simp[EVERY_MEM]) >>
  fs[sw_rhs_def, sw_out_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem sw_rounds_seed:
  sw_consistent ds /\ sw_seed ds a v ==>
  a IN sw_rounds ds 1 v
Proof
  rw[sw_seed_def] >>
  pure_rewrite_tac[numLib.num_CONV ``1``, sw_rounds_def] >>
  irule sw_scan_member >> metis_tac[sw_bottom_admissible]
QED

Theorem sw_rounds_edge:
  sw_consistent ds /\ sw_edge ds x y /\ a IN sw_rounds ds n x ==>
  a IN sw_rounds ds (SUC n) y
Proof
  rw[sw_edge_def] >> simp[Once sw_rounds_def] >>
  irule sw_scan_member >> metis_tac[sw_rounds_admissible]
QED

(* Each base evolves independently: offsets or other bases cannot affect it. *)
Theorem sw_rhs_member_cong:
  (!v. (a IN X v <=> a IN Y v)) ==>
  (a IN sw_rhs d X <=> a IN sw_rhs d Y)
Proof
  Cases_on `d` >> Cases_on `r` >>
  rw[sw_rhs_def] >> metis_tac[]
QED

Theorem sw_scan_member_cong:
  !stream X Y. (!v. (a IN X v <=> a IN Y v)) ==>
    !v. (a IN sw_scan stream X v <=> a IN sw_scan stream Y v)
Proof
  Induct >> simp[sw_scan_def] >> rpt strip_tac >>
  first_x_assum irule >> gen_tac >> simp[sw_update_def] >>
  metis_tac[sw_rhs_member_cong]
QED

Theorem sw_scan_nonwriter:
  !stream X. ~MEM v (MAP sw_out stream) ==> sw_scan stream X v = X v
Proof
  Induct >> simp[sw_scan_def, sw_update_def]
QED

Theorem sw_rounds_nonwriter:
  !n. ~(v IN IMAGE sw_out (set ds)) ==> sw_rounds ds n v = {}
Proof
  Induct >> simp[sw_rounds_def] >> rpt strip_tac >>
  `~MEM v (MAP sw_out ds)` by simp[MEM_MAP] >>
  simp[sw_scan_nonwriter] >> first_x_assum irule >> simp[IN_IMAGE]
QED

Definition sw_coverage_def:
  sw_coverage ds a n = {v | a IN sw_rounds ds n v}
End

Theorem sw_coverage_carrier:
  sw_coverage ds a n SUBSET IMAGE sw_out (set ds)
Proof
  pure_rewrite_tac[sw_coverage_def, SUBSET_DEF, GSPECIFICATION] >>
  rpt strip_tac >> spose_not_then assume_tac >>
  drule sw_rounds_nonwriter >> disch_then (qspec_then `n` mp_tac) >>
  strip_tac >> gvs[]
QED

Theorem sw_coverage_finite:
  FINITE (sw_coverage ds a n)
Proof
  irule SUBSET_FINITE >>
  qexists_tac `IMAGE sw_out (set ds)` >> simp[sw_coverage_carrier]
QED

Theorem sw_coverage_mono:
  sw_consistent ds /\ m <= n ==>
  sw_coverage ds a m SUBSET sw_coverage ds a n
Proof
  strip_tac >> drule_all sw_rounds_mono >>
  simp[sw_le_def, sw_coverage_def, SUBSET_DEF]
QED

Theorem sw_coverage_plateau_step:
  sw_coverage ds a (SUC n) = sw_coverage ds a n ==>
  sw_coverage ds a (SUC (SUC n)) = sw_coverage ds a (SUC n)
Proof
  simp_tac (srw_ss()) [sw_coverage_def, EXTENSION] >> strip_tac >>
  drule sw_scan_member_cong >> disch_then (qspec_then `ds` assume_tac) >>
  fs[sw_rounds_def]
QED

Theorem sw_coverage_strict_count:
  !n. sw_consistent ds /\
    sw_coverage ds a (SUC n) <> sw_coverage ds a n ==>
    n < CARD (sw_coverage ds a (SUC n))
Proof
  Induct
  >- (rpt strip_tac >>
      `sw_coverage ds a 0 = {}` by simp[sw_coverage_def, sw_rounds_def] >>
      spose_not_then assume_tac >>
      `CARD (sw_coverage ds a (SUC 0)) = 0` by decide_tac >>
      metis_tac[sw_coverage_finite, CARD_EQ_0]) >>
  rpt strip_tac >>
  `sw_coverage ds a (SUC n) <> sw_coverage ds a n` by
    metis_tac[sw_coverage_plateau_step] >>
  `n < CARD (sw_coverage ds a (SUC n))` by metis_tac[] >>
  `sw_coverage ds a (SUC n) PSUBSET sw_coverage ds a (SUC (SUC n))` by
    (simp[PSUBSET_DEF] >> irule sw_coverage_mono >> simp[]) >>
  `CARD (sw_coverage ds a (SUC n)) <
   CARD (sw_coverage ds a (SUC (SUC n)))` by
    metis_tac[CARD_PSUBSET, sw_coverage_finite] >>
  decide_tac
QED

Theorem sw_coverage_stable:
  sw_consistent ds ==>
  sw_coverage ds a (SUC (CARD (IMAGE sw_out (set ds)))) =
  sw_coverage ds a (CARD (IMAGE sw_out (set ds)))
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule_all sw_coverage_strict_count >>
  `CARD (sw_coverage ds a (SUC (CARD (IMAGE sw_out (set ds))))) <=
   CARD (IMAGE sw_out (set ds))` by
    (irule CARD_SUBSET >> simp[sw_coverage_carrier]) >>
  decide_tac
QED

Theorem sw_rounds_stable:
  sw_consistent ds ==>
  sw_rounds ds (SUC (CARD (IMAGE sw_out (set ds)))) =
  sw_rounds ds (CARD (IMAGE sw_out (set ds)))
Proof
  strip_tac >> irule EQ_EXT >> qx_gen_tac `v` >>
  simp_tac (srw_ss()) [EXTENSION] >> qx_gen_tac `a` >>
  drule sw_coverage_stable >> disch_then (qspec_then `a` mp_tac) >>
  simp[sw_coverage_def, EXTENSION] >> metis_tac[]
QED

Theorem sw_rounds_stationary:
  sw_rounds ds (SUC n) = sw_rounds ds n ==>
  !k. sw_rounds ds (n + k) = sw_rounds ds n
Proof
  strip_tac >> Induct >> simp[arithmeticTheory.ADD_CLAUSES, sw_rounds_def] >>
  fs[sw_rounds_def]
QED

Theorem sw_rounds_bound:
  sw_consistent ds ==>
  sw_le (sw_rounds ds n) (sw_rounds ds (CARD (IMAGE sw_out (set ds))))
Proof
  strip_tac >> Cases_on `n <= CARD (IMAGE sw_out (set ds))`
  >- metis_tac[sw_rounds_mono] >>
  drule sw_rounds_stable >> disch_then (mp_then Any mp_tac sw_rounds_stationary) >>
  disch_then (qspec_then `n - CARD (IMAGE sw_out (set ds))` mp_tac) >>
  `CARD (IMAGE sw_out (set ds)) + (n - CARD (IMAGE sw_out (set ds))) = n` by
    decide_tac >>
  simp[sw_le_def]
QED

(* Arbitrarily long dependency chains need no further rounds. *)
Theorem sw_rounds_reachable:
  !x y. RTC (sw_edge ds) x y ==>
  sw_consistent ds /\ sw_seed ds a x ==>
  a IN sw_rounds ds (CARD (IMAGE sw_out (set ds))) y
Proof
  ho_match_mp_tac relationTheory.RTC_INDUCT_RIGHT1 >>
  conj_tac >- (rpt strip_tac >>
    drule_all sw_rounds_seed >>
    drule sw_rounds_bound >> simp[sw_le_def, SUBSET_DEF] >> metis_tac[]) >>
  rpt strip_tac >>
  `a IN sw_rounds ds (CARD (IMAGE sw_out (set ds))) y` by metis_tac[] >>
  drule_all sw_rounds_edge >> strip_tac >>
  drule sw_rounds_stable >> strip_tac >> gvs[]
QED

(* A membership-fixed admissible scan is locally stationary at every writer. *)
Theorem sw_fixed_writer_member:
  sw_consistent ds /\ sw_admissible ds X /\
  (!v. t IN sw_scan ds X v <=> t IN X v) /\ MEM d ds ==>
  (t IN sw_rhs d X <=> t IN X (sw_out d))
Proof
  strip_tac >>
  `sw_rhs d X SUBSET sw_scan ds X (sw_out d)` by
    (irule sw_scan_covers_rhs >> simp[] >> qexists `ds` >> simp[EVERY_MEM]) >>
  fs[sw_admissible_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem sw_fixed_stream_member:
  !stream X.
  sw_consistent ds /\ sw_admissible ds X /\
  (!v. t IN sw_scan ds X v <=> t IN X v) /\
  EVERY (\d. MEM d ds) stream ==>
  !v. t IN sw_scan stream X v <=> t IN X v
Proof
  Induct >> simp[sw_scan_def] >> rpt strip_tac >>
  `!v. t IN sw_update h X v <=> t IN X v` by
    (gen_tac >> simp[sw_update_def] >>
     metis_tac[sw_fixed_writer_member]) >>
  `!v. t IN sw_scan stream (sw_update h X) v <=> t IN sw_scan stream X v` by
    (irule sw_scan_member_cong >> simp[]) >>
  `!v. t IN sw_scan stream X v <=> t IN X v` by
    (first_x_assum irule >> simp[]) >>
  metis_tac[]
QED
