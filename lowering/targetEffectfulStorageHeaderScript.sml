Theory targetEffectfulStorageHeader
Ancestors
  accountsRelProps vyperStorageLayoutSafety vyperStorageBackend
  vyperStoragePlaceProvenance loweringStateRelDefs

Theorem declared_region_post_index_slots:
  declared_storage_region cx mid name subs = SOME (tr,slot,tv) /\
  contract_storage_well_formed cx ef ==>
  slots_in_range (get_storage cx ef tr) (w2n slot) tv
Proof
  strip_tac >> irule contract_storage_well_formed_region >>
  simp[get_storage_backend_eq] >> metis_tac[]
QED
