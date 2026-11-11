Theory targetStorageWriteFrame
Ancestors
  vyperStorageLayoutSafety vyperStorageWritePreservation vyperStorageBackend
  vyperStoragePlaceRegion vyperStorageFrame vyperStorage
  vfmState arithmetic combin

Theorem declared_capacity_typed_write_frame:
  storage_layout_safe cx /\
  declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
  declared_storage_region cx mid' name' keys' = SOME (tr',root',rtv') /\
  (mid,name,keys) <> (mid',name',keys') /\
  storage_subregion rtv path delta tv /\
  w2n slot = w2n root + delta /\
  value_has_type tv v /\
  write_storage_slot cx tr slot tv v es = (INL (),ef) /\
  w2n root' <= q /\ q < w2n root' + type_slot_size rtv' ==>
  lookup_storage (n2w q) (get_storage cx ef tr') =
  lookup_storage (n2w q) (get_storage cx es tr')
Proof
  strip_tac >> Cases_on `tr = tr'`
  >- (gvs[] >>
      drule storage_subregion_bounds >> strip_tac >>
      `ranges_disjoint (w2n root) (type_slot_size rtv)
         (w2n root') (type_slot_size rtv')` by
        (fs[storage_layout_safe_def] >> metis_tac[]) >>
      `ranges_disjoint (w2n slot) (type_slot_size tv) q 1` by
        (fs[ranges_disjoint_def] >> decide_tac) >>
      drule_all typed_write_storage_slot_preserves_disjoint_read_slot >>
      simp[read_slot_def]) >>
  gvs[write_storage_slot_eq, AllCaseEqs()] >>
  simp[get_storage_after_set_other]
QED

(* A Pop's header update is this primitive with value = n2w (len - 1).
   The protected range includes headers and unused array capacity. *)
Theorem declared_capacity_header_update_frame:
  storage_layout_safe cx /\
  declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
  declared_storage_region cx mid' name' keys' = SOME (tr',root',rtv') /\
  (mid,name,keys) <> (mid',name',keys') /\
  w2n root <= w2n slot /\ w2n slot < w2n root + type_slot_size rtv /\
  w2n root' <= q /\ q < w2n root' + type_slot_size rtv' ==>
  lookup_storage (n2w q)
    (get_storage cx (set_storage cx es tr
      (update_storage slot value (get_storage cx es tr))) tr') =
  lookup_storage (n2w q) (get_storage cx es tr')
Proof
  strip_tac >> Cases_on `tr = tr'`
  >- (gvs[get_storage_after_set] >>
      `ranges_disjoint (w2n root) (type_slot_size rtv)
         (w2n root') (type_slot_size rtv')` by
        (fs[storage_layout_safe_def] >> metis_tac[]) >>
      `slot <> (n2w q:bytes32)` by
        (strip_tac >> gvs[storage_layout_safe_def, ranges_disjoint_def] >>
         `q < dimword (:256)` by metis_tac[LESS_LESS_EQ_TRANS] >>
         gvs[wordsTheory.w2n_n2w, LESS_MOD] >> decide_tac) >>
      simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]) >>
  simp[get_storage_after_set_other]
QED
