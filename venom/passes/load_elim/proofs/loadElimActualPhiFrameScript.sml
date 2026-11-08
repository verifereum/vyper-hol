Theory loadElimActualPhiFrame
Ancestors
  loadElimPhiTransport loadElimMemoryRel loadElimPaddedSimHelpers loadElimDynamicCapture
  loadElimHistoryHelpers loadElimOperationalHistory venomState stateFrame
  list finite_map pred_set

Theorem padded_exec_equiv_update_fresh_right:
  v IN vars /\ padded_exec_equiv vars s t ==>
  padded_exec_equiv vars s (update_var v w t)
Proof
  simp[padded_exec_equiv_def, lookup_var_def, update_var_def,
       read_memory_def, execution_frame_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* All reads use t, not the recursively updated state. *)
Theorem le_snapshot_batch_fresh_right:
  !ys t s.
    padded_exec_equiv vars s t /\
    (!j. MEM j ys ==> ?v w. read t j = SOME (v,w) /\ v IN vars) ==>
    ?q. le_snapshot_batch read t ys = SOME q /\ padded_exec_equiv vars s q
Proof
  Induct >- simp[le_snapshot_batch_def] >>
  rpt gen_tac >> strip_tac >>
  `?v w. read t h = SOME (v,w) /\ v IN vars` by metis_tac[MEM] >>
  `?q. le_snapshot_batch read t ys = SOME q /\ padded_exec_equiv vars s q` by
    (first_x_assum irule >> simp[] >> metis_tac[MEM]) >>
  simp[le_snapshot_batch_def] >>
  metis_tac[padded_exec_equiv_update_fresh_right]
QED

(* Original prefix, followed by fresh generated outputs, one snapshot. *)
Theorem le_snapshot_batch_append_fresh_transport:
  !xs s t p.
    padded_exec_equiv vars s t /\
    (!j. MEM j xs ==> read s j = read t j) /\
    le_snapshot_batch read s xs = SOME p /\
    (!j. MEM j ys ==> ?v w. read t j = SOME (v,w) /\ v IN vars) ==>
    ?q. le_snapshot_batch read t (xs ++ ys) = SOME q /\
        padded_exec_equiv vars p q
Proof
  Induct >- (simp[le_snapshot_batch_def] >>
    metis_tac[le_snapshot_batch_fresh_right]) >>
  rpt gen_tac >> strip_tac >>
  gvs[le_snapshot_batch_def, AllCaseEqs()] >>
  `read t h = SOME (out,value)` by metis_tac[MEM] >>
  `?q. le_snapshot_batch read t (xs ++ ys) = SOME q /\
       padded_exec_equiv vars t' q` by
    (first_x_assum irule >> simp[] >> metis_tac[MEM]) >>
  simp[le_snapshot_batch_def] >>
  metis_tac[padded_exec_equiv_update_var]
QED
