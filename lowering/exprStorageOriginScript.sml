(* Current-read provenance at effect-free source expression origins. *)
Theory exprStorageOrigin
Ancestors
  accountsRelProps vyperStoragePlaceProvenance vyperStorageBackend
  supportedExprTraverse vyperStatePreservation

Definition storage_result_live_def:
  storage_result_live cx es (PlaceR (StoragePlace tr slot tv)) =
    (storage_read_live cx tr (get_storage cx es tr) slot tv /\
     slots_in_range (get_storage cx es tr) (w2n slot) tv) /\
  storage_result_live cx es (HashMapRef tr slot kt vt) =
    storage_mapping_region cx tr slot (HashMapT kt vt) /\
  storage_result_live cx es _ = T
End

Theorem declared_storage_region_live:
  contract_storage_well_formed cx es /\
  declared_storage_region cx mid id keys = SOME (tr,slot,tv) ==>
  storage_result_live cx es (PlaceR (StoragePlace tr slot tv))
Proof
  strip_tac >> simp[storage_result_live_def] >>
  conj_tac >- metis_tac[declared_storage_region_read_live] >>
  fs[vyperStorageLayoutSafetyTheory.contract_storage_well_formed_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  simp[get_storage_backend_eq]
QED

Theorem lookup_global_result_live:
  contract_storage_well_formed cx es /\
  lookup_global cx mid id es = (INL r,es') ==>
  storage_result_live cx es' r
Proof
  strip_tac >> drule lookup_global_state >> strip_tac >> gvs[] >>
  Cases_on `r` >> simp[storage_result_live_def]
  >- (Cases_on `p` >> simp[storage_result_live_def] >>
      drule lookup_global_storage_region >> strip_tac >>
      drule_all declared_storage_region_live >> simp[storage_result_live_def])
  >> metis_tac[lookup_global_mapping_region]
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Storage origin dependency" else ()
  end) [declared_storage_region_live, lookup_global_result_live];
