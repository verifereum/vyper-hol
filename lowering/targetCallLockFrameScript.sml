Theory targetCallLockFrame
Ancestors
  vyperTypeEvalStoragePreservation vyperStorageBackend vyperStorageLayoutSafety
  vyperStorageFrame vyperInterpreter vyperState vfmExecution vfmState
  words arithmetic combin

Theorem acquire_lock_get_storage_frame:
  acquire_nonreentrant_lock cx.txn.target slot view st = (res,st') /\
  (~tr \/ w <> n2w slot) ==>
  lookup_storage w (get_storage cx st' tr) =
  lookup_storage w (get_storage cx st tr)
Proof
  strip_tac >> drule acquire_nonreentrant_lock_frame >> strip_tac >>
  Cases_on `tr` >> gvs[get_storage_def, lookup_transient_storage_def]
QED

Theorem release_lock_get_storage_frame:
  release_nonreentrant_lock cx.txn.target slot st = (res,st') /\
  (~tr \/ w <> n2w slot) ==>
  lookup_storage w (get_storage cx st' tr) =
  lookup_storage w (get_storage cx st tr)
Proof
  Cases_on `tr` >>
  simp[release_nonreentrant_lock_eq, get_storage_def,
       lookup_transient_storage_def, update_transient_storage_def,
       lookup_storage_def, update_storage_def, APPLY_UPDATE_THM] >>
  rpt strip_tac >> gvs[update_transient_storage_def, APPLY_UPDATE_THM]
QED

Theorem lock_if_nr_get_storage_frame:
  lock_if_nr cx nr view st = (res,st') /\
  (~tr \/ !slot. cx.nonreentrant_slot = SOME slot ==> w <> n2w slot) ==>
  lookup_storage w (get_storage cx st' tr) =
  lookup_storage w (get_storage cx st tr)
Proof
  Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
  Cases_on `view` >> Cases_on `cx.txn.is_static` >>
  simp[lock_if_nr_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, check_not_static_def,
       check_def, vyperStateTheory.assert_def, vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[acquire_lock_get_storage_frame]
QED

Theorem unlock_if_nr_get_storage_frame:
  unlock_if_nr cx nr view st = (res,st') /\
  (~tr \/ !slot. cx.nonreentrant_slot = SOME slot ==> w <> n2w slot) ==>
  lookup_storage w (get_storage cx st' tr) =
  lookup_storage w (get_storage cx st tr)
Proof
  Cases_on `nr /\ ~view` >> Cases_on `cx.nonreentrant_slot` >>
  simp[unlock_if_nr_def, vyperStateTheory.return_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[release_lock_get_storage_frame]
QED

(* Separation is over the entire declared capacity, not only live cells. *)
Theorem declared_capacity_lock_word_separation:
  storage_layout_safe cx /\ cx.nonreentrant_slot = SOME lock /\
  declared_storage_region cx mid name keys = SOME (T,root,tv) /\
  w2n root <= q /\ q < w2n root + type_slot_size tv ==>
  (n2w q : bytes32) <> n2w lock
Proof
  strip_tac >>
  drule_all storage_layout_safe_nonreentrant_slot_separation >>
  drule_all storage_layout_safe_nonreentrant_slot_nonoverflow >>
  drule_all storage_layout_safe_region_nonoverflow >>
  rpt strip_tac >>
  `q < dimword (:256) /\ lock < dimword (:256) /\ q <> lock` by
    (fs[ranges_disjoint_def] >> decide_tac) >>
  gvs[n2w_11, LESS_MOD]
QED
