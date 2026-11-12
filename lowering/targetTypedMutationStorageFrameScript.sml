Theory targetTypedMutationStorageFrame
Ancestors
  targetStorageWriteFrame vyperStorageRegionWrite vyperStorageBackend
  vyperStorageLayoutSafety vyperStoragePlaceRegion vyperStorageFrame vyperStorage vfmState arithmetic combin

Theorem declared_capacity_typed_write_frame_result:
  storage_layout_safe cx /\
  declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
  declared_storage_region cx mid' name' keys' = SOME (tr',root',rtv') /\
  (mid,name,keys) <> (mid',name',keys') /\
  storage_subregion rtv path delta tv /\
  w2n slot = w2n root + delta /\
  value_has_type tv v /\
  write_storage_slot cx tr slot tv v es = (res,ef) /\
  w2n root' <= q /\ q < w2n root' + type_slot_size rtv' ==>
  lookup_storage (n2w q) (get_storage cx ef tr') =
  lookup_storage (n2w q) (get_storage cx es tr')
Proof
  strip_tac >> Cases_on `res`
  >- (Cases_on `x` >> drule_all declared_capacity_typed_write_frame >> simp[]) >>
  gvs[write_storage_slot_eq, AllCaseEqs()]
QED

Theorem declared_capacity_pop_frame_result:
  storage_layout_safe cx /\
  declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
  declared_storage_region cx mid' name' keys' = SOME (tr',root',rtv') /\
  (mid,name,keys) <> (mid',name',keys') /\
  storage_subregion rtv path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root + delta /\
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) es = (res,ef) /\
  w2n root' <= q /\ q < w2n root' + type_slot_size rtv' ==>
  lookup_storage (n2w q) (get_storage cx ef tr') =
  lookup_storage (n2w q) (get_storage cx es tr')
Proof
  strip_tac >> drule storage_subregion_bounds >> strip_tac >>
  `w2n root + type_slot_size rtv <= dimword(:256) /\
   w2n root' + type_slot_size rtv' <= dimword(:256)` by
    (fs[storage_layout_safe_def] >> metis_tac[]) >>
  `w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256)` by decide_tac >>
  drule_all storage_pop_footprint >> strip_tac >>
  Cases_on `tr = tr'`
  >- (gvs[] >>
      `ranges_disjoint (w2n root) (type_slot_size rtv)
         (w2n root') (type_slot_size rtv')` by
        (fs[storage_layout_safe_def] >> metis_tac[]) >>
      `q < w2n slot \/ w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= q` by
        (fs[ranges_disjoint_def] >> decide_tac) >>
      `read_slot (get_storage cx ef tr) q = read_slot (get_storage cx es tr) q` by
        (first_x_assum irule >> decide_tac) >>
      gvs[read_slot_def]) >>
  `tr' = ~tr` by (Cases_on `tr` >> Cases_on `tr'` >> gvs[]) >>
  gvs[]
QED

Theorem declared_capacity_append_frame_result:
  storage_layout_safe cx /\
  declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
  declared_storage_region cx mid' name' keys' = SOME (tr',root',rtv') /\
  (mid,name,keys) <> (mid',name',keys') /\
  storage_subregion rtv path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root + delta /\ value_has_type tv v /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) v es = (res,ef) /\
  w2n root' <= q /\ q < w2n root' + type_slot_size rtv' ==>
  lookup_storage (n2w q) (get_storage cx ef tr') =
  lookup_storage (n2w q) (get_storage cx es tr')
Proof
  strip_tac >> drule storage_subregion_bounds >> strip_tac >>
  `w2n root + type_slot_size rtv <= dimword(:256) /\
   w2n root' + type_slot_size rtv' <= dimword(:256)` by
    (fs[storage_layout_safe_def] >> metis_tac[]) >>
  `w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256)` by decide_tac >>
  drule_all storage_append_footprint >> strip_tac >>
  Cases_on `tr = tr'`
  >- (gvs[] >>
      `ranges_disjoint (w2n root) (type_slot_size rtv)
         (w2n root') (type_slot_size rtv')` by
        (fs[storage_layout_safe_def] >> metis_tac[]) >>
      `q < w2n slot \/ w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= q` by
        (fs[ranges_disjoint_def] >> decide_tac) >>
      `read_slot (get_storage cx ef tr) q = read_slot (get_storage cx es tr) q` by
        (first_x_assum irule >> decide_tac) >>
      gvs[read_slot_def]) >>
  `tr' = ~tr` by (Cases_on `tr` >> Cases_on `tr'` >> gvs[]) >>
  gvs[]
QED
