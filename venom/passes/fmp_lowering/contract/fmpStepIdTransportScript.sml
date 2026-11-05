(* Occurrence-sensitive transport of retained and freshly allocated IDs. *)
Theory fmpStepIdTransport
Ancestors
  fmpStepSupply dretDesugarProofs list arithmetic

Definition ir_id_transport_def:
  ir_id_transport (B:num) lo hi src dst <=>
    B <= lo /\ lo <= hi /\ ALL_DISTINCT src /\
    EVERY (\x. x < B) src /\ ALL_DISTINCT dst /\
    EVERY (\x. MEM x src \/ (lo <= x /\ x < hi)) dst
End

Theorem ir_id_transport_empty:
  B <= lo ==> ir_id_transport B lo lo [] []
Proof
  simp[ir_id_transport_def]
QED

Theorem ir_id_transport_retained:
  x < B /\ B <= lo ==> ir_id_transport B lo lo [x] [x]
Proof
  simp[ir_id_transport_def]
QED

Theorem ir_id_transport_fresh:
  B <= lo /\ ALL_DISTINCT src /\ EVERY (\x. x < B) src /\
  ir_id_interval lo hi dst ==> ir_id_transport B lo hi src dst
Proof
  simp[ir_id_transport_def, ir_id_interval_def, EVERY_MEM] >> metis_tac[]
QED

Theorem ir_id_transport_distinct:
  ir_id_transport B lo hi src dst ==> ALL_DISTINCT dst
Proof
  simp[ir_id_transport_def]
QED

Theorem ir_id_transport_mono:
  ir_id_transport B lo hi src dst ==> lo <= hi
Proof
  simp[ir_id_transport_def]
QED

Theorem ir_id_transport_origin:
  ir_id_transport B lo hi src dst /\ MEM id dst ==>
  MEM id src \/ (lo <= id /\ id < hi)
Proof
  simp[ir_id_transport_def, EVERY_MEM] >> metis_tac[]
QED

Theorem ir_id_transport_append:
  ir_id_transport B lo mid xs us /\ ir_id_transport B mid hi ys vs /\
  ALL_DISTINCT (xs ++ ys) ==>
  ir_id_transport B lo hi (xs ++ ys) (us ++ vs)
Proof
  simp[ir_id_transport_def, EVERY_APPEND] >> rpt strip_tac
  >- (irule all_distinct_append_fresh >> simp[] >>
      gvs[EVERY_MEM, ALL_DISTINCT_APPEND] >> rpt strip_tac >>
      `MEM x xs \/ (lo <= x /\ x < mid)` by metis_tac[] >>
      `MEM x ys \/ (mid <= x /\ x < hi)` by metis_tac[] >>
      rpt strip_tac >> gvs[] >>
      metis_tac[LESS_LESS_EQ_TRANS, NOT_LESS])
  >- (gvs[EVERY_MEM] >> rpt strip_tac >>
      `MEM x xs \/ (lo <= x /\ x < mid)` by metis_tac[] >>
      gvs[] >> decide_tac) >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  `MEM x ys \/ (mid <= x /\ x < hi)` by metis_tac[] >>
  gvs[] >> decide_tac
QED

(* Definition probe: allocations need not retain any source occurrence. *)
Theorem ir_id_transport_fresh_empty_source:
  B <= lo /\ ir_id_interval lo hi dst ==>
  ir_id_transport B lo hi [] dst
Proof
  strip_tac >> irule ir_id_transport_fresh >> simp[]
QED
