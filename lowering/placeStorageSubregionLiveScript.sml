(* Dead-byte masks along capacity subregions, including inactive children. *)
Theory placeStorageSubregionLive
Ancestors
  placeStore accountsRelProps vyperStoragePlaceRegion vyperStorageRegionWrite
  vyperPlaceTyping vyperValue compileEnv words list arithmetic

Theorem storage_subregion_dead_leaf:
  !root path delta leaf. storage_subregion root path delta leaf ==>
  !st base j b. base + type_slot_size root <= dimword(:256) /\
    dead_bytes st (base+delta) leaf j b ==>
    dead_bytes st base root j b
Proof
  ho_match_mp_tac storage_subregion_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> fs[Once storage_subregion_def] >>
  rpt gen_tac >> strip_tac >>
  FIRST [rename1 `dead_bytes _ _ (ArrayTV _ (Fixed _)) _ _` >> suspend "fixed",
         rename1 `dead_bytes _ _ (ArrayTV _ (Dynamic _)) _ _` >> suspend "dynamic",
         rename1 `dead_bytes _ _ (StructTV _) _ _` >> suspend "struct",
         rename1 `dead_bytes _ _ (TupleTV _) _ _` >> suspend "tuple"]
QED
Resume storage_subregion_dead_leaf[fixed]:
  rpt gen_tac >> strip_tac >> gvs[type_slot_size_def] >>
  `Num i * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  pure_rewrite_tac[dead_bytes_def] >> qexists_tac `Num i` >> simp[] >>
  first_x_assum drule >> disch_then irule >>
  conj_tac >- decide_tac >>
  metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED
Resume storage_subregion_dead_leaf[dynamic]:
  rpt gen_tac >> strip_tac >> gvs[type_slot_size_def] >>
  `Num i * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `dead_bytes st (base'+1+Num i * type_slot_size root) root j b` by
    (first_x_assum drule >> disch_then irule >>
     conj_tac >- decide_tac >>
     metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  pure_rewrite_tac[dead_bytes_def] >> qexists_tac `Num i` >> simp[] >>
  disj2_tac >>
  qpat_assum `dead_bytes st (base'+1+_) root j b`
    (mp_tac o MATCH_MP (cj 1 dead_bytes_range)) >>
  simp[arithmeticTheory.RIGHT_ADD_DISTRIB, arithmeticTheory.LEFT_ADD_DISTRIB] >> decide_tac
QED
Resume storage_subregion_dead_leaf[struct]:
  rpt gen_tac >> strip_tac >>
  drule vyperPlaceTypingTheory.struct_field_slot_offset >> strip_tac >>
  gvs[GSYM vyperStorageRegionWriteTheory.type_slot_size_list_sum,
      vyperStorageRegionWriteTheory.type_slot_size_fields_list, type_slot_size_def,
      dead_bytes_def, place_store_dead_fields_list, MAP_APPEND, combinTheory.o_DEF] >>
  `SUM (MAP (\x. type_slot_size (SND x)) pre) =
   type_slot_size_list (MAP SND pre)` by
    simp[vyperStorageRegionWriteTheory.type_slot_size_list_sum, listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  pure_rewrite_tac[place_store_dead_list_split, dead_bytes_def] >> disj2_tac >> disj1_tac >>
  first_x_assum drule >> disch_then irule >>
  conj_tac
  >- (qpat_x_assum `base' + type_slot_size_list _ <= _` mp_tac >>
      simp[vyperStorageRegionWriteTheory.type_slot_size_list_sum, SUM_APPEND] >> decide_tac) >>
  metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED
Resume storage_subregion_dead_leaf[tuple]:
  rpt gen_tac >> strip_tac >>
  drule vyperStorageRegionWriteTheory.tuple_component_region_split >> strip_tac >>
  gvs[type_slot_size_def, dead_bytes_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  pure_rewrite_tac[place_store_dead_list_split, dead_bytes_def] >> disj2_tac >> disj1_tac >>
  first_x_assum drule >> disch_then irule >>
  conj_tac
  >- (qpat_x_assum `base' + type_slot_size_list _ <= _` mp_tac >>
      simp[vyperStorageRegionWriteTheory.type_slot_size_list_sum, SUM_APPEND] >> decide_tac) >>
  metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED
Finalise storage_subregion_dead_leaf

Theorem storage_array_dead_children_frame[local]:
  !idx n off sz tv (base:num) st' st j b.
  idx < n /\ off + sz <= type_slot_size tv /\
  base + n * type_slot_size tv <= dimword(:256) /\
  (!a. a < dimword(:256) /\
    (a < base+idx*type_slot_size tv+off \/
     base+idx*type_slot_size tv+off+sz <= a) ==>
    lookup_storage (n2w a) st' = lookup_storage (n2w a) st) /\
  (dead_bytes st' (base+idx*type_slot_size tv) tv j b <=>
   dead_bytes st (base+idx*type_slot_size tv) tv j b) ==>
  !k. k < n ==>
    (dead_bytes st' (base+k*type_slot_size tv) tv j b <=>
     dead_bytes st (base+k*type_slot_size tv) tv j b)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >> Cases_on `k = idx` >- gvs[] >>
  `k * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  irule (cj 1 dead_bytes_frame) >> rpt strip_tac >> first_x_assum irule >>
  conj_tac >- decide_tac >>
  Cases_on `k < idx`
  >- (`k * type_slot_size tv + type_slot_size tv <= idx * type_slot_size tv` by
        (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >> decide_tac) >>
  `idx * type_slot_size tv + type_slot_size tv <= k * type_slot_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >> decide_tac
QED

Theorem storage_subregion_dead_frame:
  !root path delta leaf. storage_subregion root path delta leaf ==>
  !st st' base j b. base + type_slot_size root <= dimword(:256) /\
    (!a. a < dimword(:256) /\
      (a < base+delta \/ base+delta+type_slot_size leaf <= a) ==>
      lookup_storage (n2w a) st' = lookup_storage (n2w a) st) /\
    (j < base+delta \/ base+delta+type_slot_size leaf <= j) ==>
    (dead_bytes st' base root j b <=> dead_bytes st base root j b)
Proof
  ho_match_mp_tac storage_subregion_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> fs[Once storage_subregion_def] >>
  rpt gen_tac >> strip_tac
  >- (gvs[] >> eq_tac >> strip_tac >> drule (cj 1 dead_bytes_range) >> strip_tac >> decide_tac)
  >- (gvs[] >> eq_tac >> strip_tac >> drule (cj 1 dead_bytes_range) >> strip_tac >> decide_tac) >>
  FIRST [rename1 `dead_bytes _ _ (ArrayTV _ (Fixed _)) _ _` >> suspend "fixed",
         rename1 `dead_bytes _ _ (ArrayTV _ (Dynamic _)) _ _` >> suspend "dynamic",
         rename1 `dead_bytes _ _ (StructTV _) _ _` >> suspend "struct",
         rename1 `dead_bytes _ _ (TupleTV _) _ _` >> suspend "tuple"]
QED
Resume storage_subregion_dead_frame[fixed]:
  rpt gen_tac >> strip_tac >> gvs[type_slot_size_def] >>
  `Num i * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `dead_bytes st' (base'+Num i*type_slot_size root) root j b <=>
   dead_bytes st (base'+Num i*type_slot_size root) root j b` by
    (first_x_assum drule >> disch_then irule >>
     rpt conj_tac >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  drule_at (Pat `dead_bytes _ _ _ _ _ <=> _`) storage_array_dead_children_frame >>
  disch_then (qspecl_then [`n`, `rest`, `type_slot_size leaf`] mp_tac) >>
  simp[] >> simp[dead_bytes_def] >> metis_tac[]
QED
Resume storage_subregion_dead_frame[dynamic]:
  rpt gen_tac >> strip_tac >> gvs[type_slot_size_def] >>
  `Num i * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `lookup_storage (n2w base') st' = lookup_storage (n2w base') st` by
    (first_x_assum irule >> simp[] >> decide_tac) >>
  `dead_bytes st' ((base'+1)+Num i*type_slot_size root) root j b <=>
   dead_bytes st ((base'+1)+Num i*type_slot_size root) root j b` by
    (first_x_assum drule >> disch_then irule >>
     rpt conj_tac >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  drule_at (Pat `dead_bytes _ _ _ _ _ <=> _`) storage_array_dead_children_frame >>
  disch_then (qspecl_then [`n`, `rest`, `type_slot_size leaf`] mp_tac) >>
  simp[] >> simp[dead_bytes_def] >> metis_tac[]
QED
Resume storage_subregion_dead_frame[struct]:
  rpt gen_tac >> strip_tac >>
  drule vyperPlaceTypingTheory.struct_field_slot_offset >> strip_tac >>
  gvs[GSYM vyperStorageRegionWriteTheory.type_slot_size_list_sum,
      vyperStorageRegionWriteTheory.type_slot_size_fields_list, type_slot_size_def,
      dead_bytes_def, place_store_dead_fields_list, MAP_APPEND, combinTheory.o_DEF] >>
  `SUM (MAP (\x. type_slot_size (SND x)) pre) =
   type_slot_size_list (MAP SND pre)` by
    simp[vyperStorageRegionWriteTheory.type_slot_size_list_sum, listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  pure_rewrite_tac[place_store_dead_list_split, dead_bytes_def] >>
  gvs[] >>
  `base' + type_slot_size_list (MAP SND pre) + type_slot_size elem +
   type_slot_size_list (MAP SND post) <= dimword(:256)` by
    (qpat_x_assum `base' + type_slot_size_list _ <= _` mp_tac >>
     simp[vyperStorageRegionWriteTheory.type_slot_size_list_sum, SUM_APPEND,
          vyperValueTheory.type_slot_size_def]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `dead_bytes_list st' base' (MAP SND pre) j b <=>
   dead_bytes_list st base' (MAP SND pre) j b` by
    (irule (cj 2 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  `dead_bytes_list st' (base'+type_slot_size_list (MAP SND pre)+type_slot_size elem) (MAP SND post) j b <=>
   dead_bytes_list st (base'+type_slot_size_list (MAP SND pre)+type_slot_size elem) (MAP SND post) j b` by
    (irule (cj 2 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  `dead_bytes st' (base'+type_slot_size_list (MAP SND pre)) elem j b <=>
   dead_bytes st (base'+type_slot_size_list (MAP SND pre)) elem j b` by
    (first_x_assum drule >> disch_then irule >>
     rpt conj_tac >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >> gvs[]
QED
Resume storage_subregion_dead_frame[tuple]:
  rpt gen_tac >> strip_tac >>
  drule vyperStorageRegionWriteTheory.tuple_component_region_split >> strip_tac >>
  gvs[type_slot_size_def, dead_bytes_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  pure_rewrite_tac[place_store_dead_list_split, dead_bytes_def] >>
  `base' + type_slot_size_list pre + type_slot_size elem +
   type_slot_size_list post <= dimword(:256)` by
    (qpat_x_assum `base' + type_slot_size_list _ <= _` mp_tac >>
     simp[vyperStorageRegionWriteTheory.type_slot_size_list_sum, SUM_APPEND,
          vyperValueTheory.type_slot_size_def]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `dead_bytes_list st' base' pre j b <=> dead_bytes_list st base' pre j b` by
    (irule (cj 2 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  `dead_bytes_list st' (base'+type_slot_size_list pre+type_slot_size elem) post j b <=>
   dead_bytes_list st (base'+type_slot_size_list pre+type_slot_size elem) post j b` by
    (irule (cj 2 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  `dead_bytes st' (base'+type_slot_size_list pre) elem j b <=>
   dead_bytes st (base'+type_slot_size_list pre) elem j b` by
    (first_x_assum drule >> disch_then irule >>
     rpt conj_tac >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >> simp[]
QED
Finalise storage_subregion_dead_frame
