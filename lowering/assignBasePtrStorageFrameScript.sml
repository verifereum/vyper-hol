Theory assignBasePtrStorageFrame
Ancestors
  compileEnv accountsRelProps vyperEncodeDecode vyperStorageFrame vyperStorage
  vyperValue vyperTyping vyperState vfmState words list combin arithmetic

Theorem apply_writes_lookup_untouched:
  !writes k st q.
    (!i. MEM i (MAP FST writes) ==>
         (n2w (w2n k + i):bytes32) <> q) ==>
    lookup_storage q (apply_writes k writes st) = lookup_storage q st
Proof
  Induct >> simp[apply_writes_def] >>
  Cases >> simp[apply_writes_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `q` mp_tac) >>
  simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM] >>
  metis_tac[]
QED

Theorem encoded_storage_lookup_outside:
  !tv v writes k st x.
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    x < dimword (:256) /\
    ~(w2n k <= x /\ x < w2n k + type_slot_size tv) ==>
    lookup_storage (n2w x) (apply_writes k writes st) =
    lookup_storage (n2w x) st
Proof
  rpt strip_tac >> irule apply_writes_lookup_untouched >>
  rpt strip_tac >> drule_all (cj 1 encode_writes_bounded) >>
  strip_tac >>
  `w2n k + i < dimword (:256)` by decide_tac >>
  gvs[wordsTheory.n2w_11, LESS_MOD] >> decide_tac
QED

Theorem storage_dead_encoded_outside:
  !cx tr mid n subs k tv v writes st x b.
    declared_storage_region cx mid n subs = SOME (tr,k,tv) /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    ~(w2n k <= x /\ x < w2n k + type_slot_size tv) /\
    storage_dead cx tr st x b ==>
    storage_dead cx tr (apply_writes k writes st) x b
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `storage_dead _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[storage_dead_def] >> strip_tac >>
  rename1 `dead_bytes st (w2n slot) tv' x b` >>
  `(slot,tv') <> (k,tv)` by
    (strip_tac >> gvs[] >> drule (cj 1 dead_bytes_range) >> simp[]) >>
  `ranges_disjoint (w2n slot) (type_slot_size tv')
     (w2n k) (type_slot_size tv)` by
    (first_x_assum irule >> metis_tac[]) >>
  `dead_bytes (apply_writes k writes st) (w2n slot) tv' x b <=>
   dead_bytes st (w2n slot) tv' x b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     irule encoded_storage_lookup_outside >>
     conj_tac >- decide_tac >>
     qexistsl_tac [`tv`, `v`] >>
     gvs[vyperStorageFrameTheory.ranges_disjoint_def] >> decide_tac) >>
  qexistsl_tac [`mid'`, `n'`, `subs'`, `slot`, `tv'`] >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[] >> metis_tac[]
QED

Theorem storage_dead_lookup_cong:
  !cx tr st final j b.
    (!i. lookup_storage (n2w i) final = lookup_storage (n2w i) st) ==>
    (storage_dead cx tr final j b <=> storage_dead cx tr st j b)
Proof
  rpt strip_tac >> simp[storage_dead_def] >>
  `!base tv. dead_bytes final base tv j b <=> dead_bytes st base tv j b` by
    (rpt strip_tac >> irule (cj 1 dead_bytes_frame) >> simp[]) >>
  metis_tac[]
QED

Theorem storage_dead_encoded_endpoint_outside:
  !cx tr mid n subs k tv v writes st final x b.
    declared_storage_region cx mid n subs = SOME (tr,k,tv) /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    (!i. lookup_storage (n2w i) final =
         lookup_storage (n2w i) (apply_writes k writes st)) /\
    ~(w2n k <= x /\ x < w2n k + type_slot_size tv) /\
    storage_dead cx tr st x b ==>
    storage_dead cx tr final x b
Proof
  rpt strip_tac >>
  `storage_dead cx tr final x b <=>
   storage_dead cx tr (apply_writes k writes st) x b` by
    (irule storage_dead_lookup_cong >> simp[]) >>
  metis_tac[storage_dead_encoded_outside]
QED

(* Exterior framing uses the real endpoint only outside the destination.
   No equality with canonical dead padding inside it is needed. *)
Theorem storage_dead_endpoint_outside:
  !cx tr mid n subs k tv st final x b.
    declared_storage_region cx mid n subs = SOME (tr,k,tv) /\
    (!i. i < dimword (:256) /\
         ~(w2n k <= i /\ i < w2n k + type_slot_size tv) ==>
         lookup_storage (n2w i) final = lookup_storage (n2w i) st) /\
    ~(w2n k <= x /\ x < w2n k + type_slot_size tv) /\
    storage_dead cx tr st x b ==>
    storage_dead cx tr final x b
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `storage_dead _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[storage_dead_def] >> strip_tac >>
  rename1 `dead_bytes st (w2n slot) tv' x b` >>
  `(slot,tv') <> (k,tv)` by
    (strip_tac >> gvs[] >> drule (cj 1 dead_bytes_range) >> simp[]) >>
  `ranges_disjoint (w2n slot) (type_slot_size tv')
     (w2n k) (type_slot_size tv)` by
    (first_x_assum irule >> metis_tac[]) >>
  `dead_bytes final (w2n slot) tv' x b <=>
   dead_bytes st (w2n slot) tv' x b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >>
     gvs[vyperStorageFrameTheory.ranges_disjoint_def] >> decide_tac) >>
  qexistsl_tac [`mid'`, `n'`, `subs'`, `slot`, `tv'`] >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[] >> metis_tac[]
QED
