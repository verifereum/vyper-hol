(* Dead-byte masks through rooted storage-place paths. *)
Theory storageSubregionAgreement
Ancestors
  placeStore accountsRelProps vyperStoragePlaceRegion vyperStorageRegionWrite
  compileEnv vyperValue arithmetic list

Theorem storage_subregion_dead_bytes:
  !root path delta leaf. storage_subregion root path delta leaf ==>
    !st base j b. base + type_slot_size root <= dimword(:256) /\
      dead_bytes st (base+delta) leaf j b ==>
      dead_bytes st base root j b
Proof
  ho_match_mp_tac storage_subregion_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  fs[Once storage_subregion_def] >> rpt gen_tac >> strip_tac >>
  FIRST [rename1 `dead_bytes _ _ (ArrayTV _ (Fixed _)) _ _` >> suspend "fixed",
         rename1 `dead_bytes _ _ (ArrayTV _ (Dynamic _)) _ _` >> suspend "dynamic",
         rename1 `dead_bytes _ _ (StructTV _) _ _` >> suspend "struct",
         rename1 `dead_bytes _ _ (TupleTV _) _ _` >> suspend "tuple"]
QED

Resume storage_subregion_dead_bytes[fixed]:
  rpt gen_tac >> strip_tac >> gvs[type_slot_size_def] >>
  `Num i * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  simp[dead_bytes_def] >> qexists `Num i` >> simp[] >>
  first_x_assum drule >> disch_then irule >>
  simp[AC ADD_ASSOC ADD_COMM] >> decide_tac
QED
Resume storage_subregion_dead_bytes[dynamic]:
  rpt gen_tac >> strip_tac >> gvs[type_slot_size_def] >>
  `Num i * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `dead_bytes st (base' + 1 + Num i * type_slot_size root) root j b` by
    (first_x_assum drule >> disch_then irule >>
     simp[]) >>
  simp[dead_bytes_def] >> qexists `Num i` >> simp[] >>
  IF_CASES_TAC >- gvs[] >>
  drule (cj 1 dead_bytes_range) >> simp[RIGHT_ADD_DISTRIB]
QED
Resume storage_subregion_dead_bytes[struct]:
  rpt gen_tac >> strip_tac >>
  drule vyperPlaceTypingTheory.struct_field_slot_offset >> strip_tac >>
  gvs[GSYM type_slot_size_list_sum, type_slot_size_fields_list,
      type_slot_size_def, dead_bytes_def, place_store_dead_fields_list,
      MAP_APPEND, combinTheory.o_DEF] >>
  `SUM (MAP (\x. type_slot_size (SND x)) pre) =
   type_slot_size_list (MAP SND pre)` by
    simp[type_slot_size_list_sum, MAP_MAP_o, combinTheory.o_DEF] >>
  `dead_bytes st (base' + type_slot_size_list (MAP SND pre)) elem j b` by
    (first_x_assum drule >> disch_then irule >>
     conj_tac
     >- (qpat_x_assum `base' + type_slot_size_list _ <= _` mp_tac >>
         simp[type_slot_size_list_sum, SUM_APPEND, type_slot_size_def]) >>
     qpat_x_assum `dead_bytes _ _ _ _ _` mp_tac >>
     asm_rewrite_tac [] >> metis_tac[ADD_ASSOC, ADD_COMM]) >>
  simp[place_store_dead_list_split, dead_bytes_def]
QED
Resume storage_subregion_dead_bytes[tuple]:
  rpt gen_tac >> strip_tac >>
  drule tuple_component_region_split >> strip_tac >>
  gvs[type_slot_size_def, dead_bytes_def] >>
  `dead_bytes st (base' + type_slot_size_list pre) elem j b` by
    (first_x_assum drule >> disch_then irule >>
     simp[] >>
     qpat_x_assum `base' + type_slot_size_list _ <= _` mp_tac >>
     simp[type_slot_size_list_sum, SUM_APPEND, type_slot_size_def]) >>
  simp[place_store_dead_list_split, dead_bytes_def]
QED
Finalise storage_subregion_dead_bytes

Theorem storage_subregion_dead_bytes_outside:
  !root path delta leaf. storage_subregion root path delta leaf ==>
    !st st' base j b. base + type_slot_size root <= dimword(:256) /\
      (!a. a < dimword(:256) /\
           (a < base+delta \/ base+delta+type_slot_size leaf <= a) ==>
           lookup_storage (n2w a) st' = lookup_storage (n2w a) st) /\
      (j < base+delta \/ base+delta+type_slot_size leaf <= j) ==>
      (dead_bytes st' base root j b <=> dead_bytes st base root j b)
Proof
  ho_match_mp_tac storage_subregion_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  fs[Once storage_subregion_def] >> rpt gen_tac >> strip_tac
  >- (eq_tac >> strip_tac >> drule (cj 1 dead_bytes_range) >> decide_tac)
  >- (eq_tac >> strip_tac >> drule (cj 1 dead_bytes_range) >> decide_tac)
  >> FIRST [rename1 `dead_bytes _ _ (ArrayTV _ (Fixed _)) _ _` >> suspend "fixed",
            rename1 `dead_bytes _ _ (ArrayTV _ (Dynamic _)) _ _` >> suspend "dynamic",
            rename1 `dead_bytes _ _ (StructTV _) _ _` >> suspend "struct",
            rename1 `dead_bytes _ _ (TupleTV _) _ _` >> suspend "tuple"]
QED
Resume storage_subregion_dead_bytes_outside[fixed]:
  rpt gen_tac >> strip_tac >>
  drule_all storage_subregion_bounds >> strip_tac >>
  gvs[type_slot_size_def] >>
  `Num i * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `!a. a < n ==>
    (dead_bytes st' (base' + a * type_slot_size root) root j b <=>
     dead_bytes st (base' + a * type_slot_size root) root j b)` by
    (rpt strip_tac >> Cases_on `a = Num i`
     >- (gvs[] >> first_x_assum drule >> disch_then irule >>
         conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
         decide_tac) >>
     `a * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
       (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
     irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >> conj_tac >- decide_tac >>
     Cases_on `a < Num i`
     >- (`a * type_slot_size root + type_slot_size root <= Num i * type_slot_size root` by
           (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
         decide_tac) >>
     `Num i < a` by decide_tac >>
     `Num i * type_slot_size root + type_slot_size root <= a * type_slot_size root` by
       (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
     decide_tac) >>
  pure_rewrite_tac[dead_bytes_def] >>
  qpat_x_assum `!a. a < n ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
Resume storage_subregion_dead_bytes_outside[dynamic]:
  rpt gen_tac >> strip_tac >>
  drule_all storage_subregion_bounds >> strip_tac >>
  gvs[type_slot_size_def] >>
  `Num i * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `lookup_storage (n2w base') st' = lookup_storage (n2w base') st` by
    (first_x_assum irule >> simp[]) >>
  `!a. a < n ==>
    (dead_bytes st' (base' + 1 + a * type_slot_size root) root j b <=>
     dead_bytes st (base' + 1 + a * type_slot_size root) root j b)` by
    (rpt strip_tac >> Cases_on `a = Num i`
     >- (gvs[] >> first_x_assum drule >> disch_then irule >>
         conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
         decide_tac) >>
     `a * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
       (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
     irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >> conj_tac >- decide_tac >>
     Cases_on `a < Num i`
     >- (`a * type_slot_size root + type_slot_size root <= Num i * type_slot_size root` by
           (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
         decide_tac) >>
     `Num i < a` by decide_tac >>
     `Num i * type_slot_size root + type_slot_size root <= a * type_slot_size root` by
       (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
     decide_tac) >>
  pure_rewrite_tac[dead_bytes_def] >> asm_rewrite_tac[] >>
  qpat_x_assum `!a. a < n ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
Resume storage_subregion_dead_bytes_outside[struct]:
  rpt gen_tac >> strip_tac >>
  drule_all storage_subregion_bounds >> strip_tac >>
  drule vyperPlaceTypingTheory.struct_field_slot_offset >> strip_tac >>
  gvs[GSYM type_slot_size_list_sum, type_slot_size_fields_list,
      type_slot_size_def, dead_bytes_def, place_store_dead_fields_list,
      MAP_APPEND, combinTheory.o_DEF] >>
  `SUM (MAP (\x. type_slot_size (SND x)) pre) =
   type_slot_size_list (MAP SND pre)` by
    simp[type_slot_size_list_sum, MAP_MAP_o, combinTheory.o_DEF] >>
  `type_slot_size_list (MAP SND pre ++ elem::MAP SND post) =
   type_slot_size_list (MAP SND pre) + type_slot_size elem + type_slot_size_list (MAP SND post)` by
    simp[type_slot_size_list_sum, MAP_APPEND, SUM_APPEND, type_slot_size_def] >>
  `dead_bytes st' (base' + type_slot_size_list (MAP SND pre)) elem j b <=>
   dead_bytes st (base' + type_slot_size_list (MAP SND pre)) elem j b` by
    (first_x_assum drule >> disch_then irule >>
     conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >> decide_tac) >>
  `dead_bytes_list st' base' (MAP SND pre) j b <=> dead_bytes_list st base' (MAP SND pre) j b` by
    (irule (cj 2 dead_bytes_frame) >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `dead_bytes_list st' (base' + type_slot_size_list (MAP SND pre) + type_slot_size elem) (MAP SND post) j b <=>
   dead_bytes_list st (base' + type_slot_size_list (MAP SND pre) + type_slot_size elem) (MAP SND post) j b` by
    (irule (cj 2 dead_bytes_frame) >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `type_slot_size_list (MAP SND pre ++ [elem]) = type_slot_size_list (MAP SND pre) + type_slot_size elem` by
    simp[type_slot_size_list_sum, MAP_APPEND, SUM_APPEND] >>
  qpat_x_assum `type_slot_size_list (_ ++ [elem]) = _` mp_tac >>
  qpat_x_assum `dead_bytes_list st' (_ + _) (MAP SND post) _ _ <=> _` mp_tac >>
  qpat_x_assum `dead_bytes_list st' base' (MAP SND pre) _ _ <=> _` mp_tac >>
  qpat_x_assum `dead_bytes st' _ elem _ _ <=> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[place_store_dead_list_split, dead_bytes_def]
QED
Resume storage_subregion_dead_bytes_outside[tuple]:
  rpt gen_tac >> strip_tac >>
  drule_all storage_subregion_bounds >> strip_tac >>
  drule tuple_component_region_split >> strip_tac >>
  gvs[type_slot_size_def, dead_bytes_def] >>
  `type_slot_size_list (pre ++ elem::post) =
   type_slot_size_list pre + type_slot_size elem + type_slot_size_list post` by
    simp[type_slot_size_list_sum, SUM_APPEND, type_slot_size_def] >>
  `dead_bytes st' (base' + type_slot_size_list pre) elem j b <=>
   dead_bytes st (base' + type_slot_size_list pre) elem j b` by
    (first_x_assum drule >> disch_then irule >>
     conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     decide_tac) >>
  `dead_bytes_list st' base' pre j b <=> dead_bytes_list st base' pre j b` by
    (irule (cj 2 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `dead_bytes_list st' (base' + type_slot_size_list pre + type_slot_size elem) post j b <=>
   dead_bytes_list st (base' + type_slot_size_list pre + type_slot_size elem) post j b` by
    (irule (cj 2 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `type_slot_size_list (pre ++ [elem]) = type_slot_size_list pre + type_slot_size elem` by
    simp[type_slot_size_list_sum, MAP_APPEND, SUM_APPEND] >>
  qpat_x_assum `type_slot_size_list (pre ++ [elem]) = _` mp_tac >>
  qpat_x_assum `dead_bytes_list st' (_ + _) post _ _ <=> _` mp_tac >>
  qpat_x_assum `dead_bytes_list st' base' pre _ _ <=> _` mp_tac >>
  qpat_x_assum `dead_bytes st' _ elem _ _ <=> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[place_store_dead_list_split, dead_bytes_def]
QED
Finalise storage_subregion_dead_bytes_outside
