(* A typed word write reconstructs the observed struct root and preserves
   the horizon's dead-byte mask. *)
Theory augAssignFullFieldStore
Ancestors
  accountsRelProps vyperStorageFootprint vyperStoragePlaceRegion
  vyperStorageRegionWrite vyperStorageBackend vyperValue
  words list arithmetic

Theorem storage_struct_field_word_write_frame:
  regions_consistent (FST H) /\
  storage_well_formed_on cx es (FST H) /\
  MEM (tr,k,StructTV fs) (FST H) /\
  struct_field_slot fs fld = SOME (off,ftv) /\
  well_formed_type_value ftv /\ type_slot_size ftv = 1 /\
  value_has_type ftv v /\
  write_storage_slot cx tr (k + n2w off) ftv v es = (INL (),ee) ==>
  storage_well_formed_on cx ee (FST H) /\
  (!w st. storage_dead H tr (update_storage (k + n2w off) w st) =
          storage_dead H tr st)
Proof
  strip_tac >>
  `storage_subregion (StructTV fs) [AttrSubscript fld] off ftv` by
    simp[storage_subregion_def] >>
  `w2n k + type_slot_size (StructTV fs) <= dimword(:256)` by
    metis_tac[regions_consistent_def] >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n k + off < dimword(:256)` by decide_tac >>
  `w2n (k + n2w off : bytes32) = w2n k + off` by
    (Cases_on `k` >> fs[word_add_n2w]) >>
  `slots_in_range (get_storage cx es tr) (w2n k) (StructTV fs)` by
    metis_tac[storage_well_formed_on_def] >>
  `0 < type_slot_size ftv` by simp[] >>
  `slots_in_range (get_storage cx ee tr) (w2n k) (StructTV fs)` by
    (drule_all storage_subregion_typed_write_preserves_root >> simp[]) >>
  conj_tac
  >- (irule contained_write_preserves_storage_well_formed_on >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`v`, `k + n2w off`, `ftv`] >> simp[] >> decide_tac) >>
  rpt gen_tac >> irule storage_dead_update_struct_word_field >> metis_tac[]
QED
