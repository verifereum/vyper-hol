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
