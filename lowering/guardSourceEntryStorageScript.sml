(* Fixed-horizon storage facts for the call entry transfer and lock. *)
Theory guardSourceEntryStorage
Ancestors
  vyperFiniteStoragePreservation vyperStorageFootprint vyperInterpreter
  vyperTypeEvalStoragePreservation vyperState

Theorem explicit_lock_observed:
  lock_if_nr cx nr is_view st = (r,u) /\
  nr /\ cx.nonreentrant_slot = SOME slot ==>
  MEM (StorageLock slot) u.storage_trace
Proof
  strip_tac >> Cases_on `is_view` >>
  gvs[lock_if_nr_def, vyperTypeEvalStoragePreservationTheory.acquire_nonreentrant_lock_eq,
      bind_def, ignore_bind_def, return_def, raise_def,
      check_not_static_def, assert_def, check_def, AllCaseEqs(), listTheory.MEM_APPEND]
QED

Theorem lock_if_nr_storage:
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H obs /\
  (!slot. nr /\ cx.nonreentrant_slot = SOME slot ==>
    MEM (StorageLock slot) obs) /\
  lock_if_nr cx nr is_view st = (r,u) ==>
  storage_well_formed_on cx u (FST H)
Proof
  reverse (Cases_on `nr`) >- (rw[lock_if_nr_def, vyperStateTheory.return_def] >> simp[]) >>
  simp[lock_if_nr_def] >>
  Cases_on `cx.nonreentrant_slot` >-
    (rw[vyperStateTheory.raise_def] >> simp[]) >>
  simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def] >>
  Cases_on `acquire_nonreentrant_lock cx.txn.target x
    (is_view \/ cx.txn.is_static) st` >>
  strip_tac >>
  `storage_well_formed_on cx r' (FST H)` by
    (drule_all acquire_lock_preserves_storage_well_formed_on >> simp[]) >>
  Cases_on `q` >> gvs[return_def] >>
  Cases_on `is_view` >> gvs[return_def, check_not_static_def,
    assert_def, check_def, raise_def]
QED

Theorem unlock_if_nr_storage:
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H obs /\
  (!slot. nr /\ cx.nonreentrant_slot = SOME slot ==>
    MEM (StorageLock slot) obs) /\
  unlock_if_nr cx nr is_view st = (r,u) ==>
  storage_well_formed_on cx u (FST H)
Proof
  reverse (Cases_on `nr /\ ~is_view`) >-
    (rw[unlock_if_nr_def, vyperStateTheory.return_def] >> simp[]) >>
  simp[unlock_if_nr_def] >>
  Cases_on `cx.nonreentrant_slot` >-
    (rw[vyperStateTheory.return_def] >> simp[]) >>
  strip_tac >>
  `MEM (StorageLock x) obs` by gvs[] >>
  gvs[] >> drule_all release_lock_preserves_storage_well_formed_on >> simp[]
QED
