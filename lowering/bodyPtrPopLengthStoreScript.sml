Theory bodyPtrPopLengthStore
Ancestors
  bodyPtrPopRegionStore bodyPtrPopRegionInvariant exprSimPopStorage ptrDiscipline pred_set
  vyperStorageBackend vfmState words

(* The general semantic dead-byte monotonicity theorem already exists as
   dead_bytes_dynarray_shorten in exprSimPopStorage.  Lift that interface to
   the captured-region observer rather than duplicate its proof. *)
Theorem pop_region_taint_shorten:
  pop_region_taint_ok st bs (ArrayTV tv (Dynamic n)) X /\
  X' SUBSET X /\
  w2n (lookup_storage (n2w bs) st') <=
    w2n (lookup_storage (n2w bs) st) /\
  (!i. bs + 1 <= i /\ i < bs + 1 + n * type_slot_size tv ==>
       lookup_storage (n2w i) st' = lookup_storage (n2w i) st) ==>
  pop_region_taint_ok st' bs (ArrayTV tv (Dynamic n)) X'
Proof
  rw[pop_region_taint_ok_def, SUBSET_DEF] >>
  irule dead_bytes_dynarray_shorten >> qexists `st` >>
  simp[] >> metis_tac[]
QED

Theorem pop_region_taint_pop_header:
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword (:256) /\
  pop_region_taint_ok st (w2n slot) (ArrayTV tv (Dynamic n)) X ==>
  pop_region_taint_ok
    (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st)
    (w2n slot) (ArrayTV tv (Dynamic n)) (key_update X slot {})
Proof
  strip_tac >> drule dead_bytes_pop_header >>
  gvs[pop_region_taint_ok_def, key_update_def] >> metis_tac[]
QED

(* An ancestor's header outside the captured interval uses the existing
   pop_region_taint_clean_store.  The paired header observation below is
   unchanged, independently of whether the ancestor length grows or shrinks. *)
Theorem pop_captured_header_outside_store:
  bs <= w2n slot /\ w2n slot < bs + type_slot_size tv /\
  (w2n key < bs \/ bs + type_slot_size tv <= w2n key) ==>
  lookup_storage slot (update_storage key value st) = lookup_storage slot st
Proof
  strip_tac >> `slot <> key` by (strip_tac >> gvs[] >> decide_tac) >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED
