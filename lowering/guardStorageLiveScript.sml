Theory guardStorageLive
Ancestors
  accountsRelProps loweringStateRelDefs vyperStorageFootprint
  vyperStorageFrame vyperValue words list

Theorem guard_storage_read_live:
  regions_consistent (FST H) /\
  EVERY (\r. MEM r (FST H)) (FST h) /\
  MEM (tr,slot,tv) (FST H) ==>
  storage_read_live h tr s slot tv
Proof
  rpt strip_tac >>
  `w2n slot + type_slot_size tv <= dimword (:256)` by
    (fs[regions_consistent_def] >> metis_tac[]) >>
  pure_rewrite_tac [storage_read_live_def] >>
  rpt gen_tac >> disch_tac >> conj_tac >- simp[] >>
  rpt strip_tac >>
  qpat_x_assum `storage_dead _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [storage_dead_def] >>
  disch_then (strip_assume_tac o CONJUNCT2) >>
  rename1 `MEM (tr,root,rtv) (FST h)` >>
  `MEM (tr,root,rtv) (FST H)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  Cases_on `(root,rtv) = (slot,tv)` >- gvs[] >>
  `ranges_disjoint (w2n root) (type_slot_size rtv)
                   (w2n slot) (type_slot_size tv)` by
    (fs[regions_consistent_def] >> metis_tac[]) >>
  drule (cj 1 dead_bytes_range) >>
  fs[ranges_disjoint_def] >> decide_tac
QED

Theorem guard_storage_transport_conditional:
  (!s off tv t.
    (!j b. off <= j /\ j < off + type_slot_size tv /\ b < 32 /\
      ~dead_bytes s off tv j b ==>
      EL b (word_to_bytes (lookup_storage (n2w j) s) T) =
      EL b (word_to_bytes (lookup_storage (n2w j) t) T)) ==>
    (slots_in_range s off tv <=> slots_in_range t off tv)) /\
  regions_consistent (FST H) /\
  EVERY (\r. MEM r (FST H)) (FST h) /\
  storage_agree (storage_dead h tr s) s t ==>
  !slot tv. MEM (tr,slot,tv) (FST H) ==>
    (slots_in_range s (w2n slot) tv <=>
     slots_in_range t (w2n slot) tv)
Proof
  rpt strip_tac >>
  `storage_read_live h tr s slot tv` by
    (irule guard_storage_read_live >> metis_tac[]) >>
  `w2n slot + type_slot_size tv <= dimword (:256)` by
    (fs[regions_consistent_def] >> metis_tac[]) >>
  `storage_range_agree s t slot tv` by
    (irule (INST_TYPE [alpha |-> ``:256``] storage_range_agree_of_live) >>
     simp[] >>
     qexistsl_tac [`h`, `tr`] >> simp[]) >>
  first_x_assum irule >> rpt strip_tac >>
  `j < dimword (:256)` by decide_tac >>
  qpat_x_assum `storage_range_agree _ _ _ _` mp_tac >>
  simp[storage_range_agree_def] >> strip_tac >>
  first_x_assum (qspecl_then [`n2w j`, `b`] mp_tac) >>
  simp[w2n_n2w, arithmeticTheory.LESS_MOD]
QED
