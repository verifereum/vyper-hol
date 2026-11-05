(* Current-read provenance at effect-free source expression origins. *)
Theory exprStorageOrigin
Ancestors
  accountsRelProps vyperStoragePlaceProvenance vyperStorageBackend
  supportedExprTraverse vyperStatePreservation vyperState

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

Theorem storage_mapping_region_live_leaf:
  contract_storage_well_formed cx es /\
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  storage_result_live cx es (PlaceR (StoragePlace tr slot tv))
Proof
  strip_tac >>
  qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >>
  rewrite_tac[storage_mapping_region_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  simp[vyperStorageLayoutSafetyTheory.resolve_hashmap_leaf_def] >> strip_tac >>
  irule declared_storage_region_live >> metis_tac[]
QED

Theorem extend_mapping_place_live:
  contract_storage_well_formed cx es /\
  storage_mapping_region cx tr slot (HashMapT kt vt) /\
  extend_place cx (HashMapRef tr slot kt vt) sb es = (INL r,es') ==>
  storage_result_live cx es' r
Proof
  Cases_on `sb` >>
  simp[extend_place_def, vyperStateTheory.raise_def] >>
  strip_tac >>
  drule storage_mapping_region_step >>
  disch_then (qspec_then `v` assume_tac) >>
  Cases_on `vt` >>
  gvs[extend_place_def, vyperStateTheory.bind_def,
      lift_option_type_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, AllCaseEqs(), storage_result_live_def] >>
  Cases_on `evaluate_type (get_tenv cx) t` >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  drule_all storage_mapping_region_live_leaf >> simp[storage_result_live_def]
QED

Theorem extend_place_result_live:
  contract_storage_well_formed cx es /\ storage_result_live cx es r /\
  extend_place cx r sb es = (INL r',es') ==>
  storage_result_live cx es' r'
Proof
  Cases_on `r` >> simp[storage_result_live_def, extend_place_def,
                       vyperStateTheory.raise_def]
  >- (Cases_on `p` >>
      simp[storage_result_live_def, extend_place_def,
           vyperStateTheory.bind_def, vyperStateTheory.return_def,
           AllCaseEqs()] >> strip_tac >>
      gvs[extend_memory_place_def, storage_result_live_def,
          vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
          vyperStateTheory.return_def, AllCaseEqs()] >>
      rename1 `extend_storage_place _ _ _ _ _ _ = (INL selected,_)` >>
      Cases_on `selected` >> simp[storage_result_live_def] >>
      drule_all extend_storage_place_read_live >>
      simp[storage_result_live_def]) >>
  metis_tac[extend_mapping_place_live]
QED

Theorem select_result_live:
  contract_storage_well_formed cx es /\ storage_result_live cx es r /\
  select_result cx ty r sb es = (INL r',es') ==>
  storage_result_live cx es' r'
Proof
  Cases_on `r` >>
  simp[select_result_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       AllCaseEqs()] >> strip_tac >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs(),
      storage_result_live_def] >>
  metis_tac[extend_place_result_live, storage_result_live_def]
QED

val _ = List.app (fn th =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if List.exists (fn s => s <> "DISK_THM") ors orelse not (null axs)
    then raise Fail "Storage selection origin dependency" else ()
  end) [storage_mapping_region_live_leaf, extend_mapping_place_live,
         extend_place_result_live, select_result_live];
