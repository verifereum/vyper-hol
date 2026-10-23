(* TOP-LEVEL: structural storage regions for typed saved-place writes.
   Helpers decompose tuple/struct layouts into a selected child and siblings. *)
Theory vyperStorageRegionWrite
Ancestors
  arithmetic list rich_list option pair words
  vyperState vyperValue vyperTyping vyperLookupStorage vyperStorageBackend
  vyperStorageFrame
  vyperStoragePlaceRegion vyperStorageWritePreservation
Libs
  wordsLib markerLib

Theorem type_slot_size_list_append:
  !pre post. type_slot_size_list (pre ++ post) =
    type_slot_size_list pre + type_slot_size_list post
Proof
  Induct >> simp[type_slot_size_def]
QED

Theorem type_slot_size_list_sum:
  !types. type_slot_size_list types = SUM (MAP type_slot_size types)
Proof
  Induct >> simp[type_slot_size_def]
QED

Theorem type_slot_size_fields_list:
  !fields. type_slot_size_fields fields = type_slot_size_list (MAP SND fields)
Proof
  Induct >> simp[type_slot_size_def] >>
  Cases_on `h` >> simp[type_slot_size_def]
QED

(* Restrict rewriting to the layout-list equations. Unfolding the entire
   mutually recursive slots_in_range definition also expands element types. *)
Theorem tuple_storage_region_equations[local]:
  tuple_slots_in_range storage off [] = T /\
  (tuple_slots_in_range storage off (tv::types) <=>
    slots_in_range storage off tv /\
    tuple_slots_in_range storage (off + type_slot_size tv) types)
Proof
  conj_tac >> pure_once_rewrite_tac [slots_in_range_def] >> simp[]
QED

Theorem struct_storage_region_equations[local]:
  struct_slots_in_range storage off [] = T /\
  (struct_slots_in_range storage off ((id,tv)::fields) <=>
    slots_in_range storage off tv /\
    struct_slots_in_range storage (off + type_slot_size tv) fields)
Proof
  conj_tac >> pure_once_rewrite_tac [slots_in_range_def] >> simp[]
QED

Theorem tuple_storage_regions_append:
  !pre post storage off.
    tuple_slots_in_range storage off (pre ++ post) <=>
    tuple_slots_in_range storage off pre /\
    tuple_slots_in_range storage (off + type_slot_size_list pre) post
Proof
  Induct >> asm_simp_tac bool_ss
    [APPEND, tuple_storage_region_equations, type_slot_size_def,
     ADD_CLAUSES, ADD_ASSOC, CONJ_ASSOC]
QED

Theorem struct_storage_regions_tuple:
  !fields storage off.
    struct_slots_in_range storage off fields <=>
    tuple_slots_in_range storage off (MAP SND fields)
Proof
  Induct >> simp[struct_storage_region_equations, tuple_storage_region_equations] >>
  Cases_on `h` >> simp[struct_storage_region_equations, tuple_storage_region_equations]
QED

Theorem tuple_component_region_split:
  oEL i types = SOME elem ==>
  ?pre post. types = pre ++ elem::post /\
    tuple_prefix_slot_size i types = type_slot_size_list pre
Proof
  strip_tac >> gvs[oEL_EQ_EL] >>
  qexistsl_tac [`TAKE i types`,`DROP (SUC i) types`] >> conj_tac
  >- (drule TAKE_DROP_SUC >> simp[APPEND_ASSOC] >> metis_tac[]) >>
  simp[tuple_prefix_slot_size_sum, type_slot_size_list_sum]
QED

Theorem slots_in_range_tuple[local]:
  slots_in_range storage off (TupleTV types) <=>
  tuple_slots_in_range storage off types
Proof
  pure_once_rewrite_tac [slots_in_range_def] >> simp[]
QED

Theorem tuple_component_typed_write_reconstruct:
  slots_in_range (get_storage cx st b) off (TupleTV (pre ++ tv::post)) /\
  0 < type_slot_size tv /\
  off + type_slot_size (TupleTV (pre ++ tv::post)) <= dimword(:256) /\
  off + type_slot_size_list pre <= w2n slot /\
  w2n slot + type_slot_size leaf <=
    off + type_slot_size_list pre + type_slot_size tv /\
  value_has_type leaf v /\
  write_storage_slot cx b slot leaf v st = (INL (),st') /\
  slots_in_range (get_storage cx st' b) (off + type_slot_size_list pre) tv ==>
  slots_in_range (get_storage cx st' b) off (TupleTV (pre ++ tv::post))
Proof
  rpt strip_tac >>
  qpat_x_assum `slots_in_range (get_storage cx st b) off (TupleTV (pre ++ tv::post))`
    (strip_assume_tac o SIMP_RULE bool_ss
      [slots_in_range_tuple, tuple_storage_regions_append,
       tuple_storage_region_equations, type_slot_size_def, ADD_ASSOC]) >>
  `off + type_slot_size_list pre + type_slot_size tv + type_slot_size_list post <=
     dimword(:256)` by
    (qpat_x_assum `off + type_slot_size (TupleTV (pre ++ tv::post)) <= _` mp_tac >>
     simp_tac bool_ss [type_slot_size_def, type_slot_size_list_append, ADD_ASSOC]) >>
  `off < dimword(:256)` by decide_tac >>
  `slots_in_range (get_storage cx st' b) off (TupleTV pre)` by
    (irule typed_write_storage_slot_preserves_disjoint_num_region >>
     asm_simp_tac bool_ss [] >>
     qexistsl_tac [`b`,`slot`,`st`,`leaf`,`v`] >>
     asm_simp_tac bool_ss [slots_in_range_tuple] >>
     simp_tac bool_ss [ranges_disjoint_def, type_slot_size_def] >> decide_tac) >>
  `slots_in_range (get_storage cx st' b)
     (off + type_slot_size_list pre + type_slot_size tv) (TupleTV post)` by
    (Cases_on `type_slot_size_list post = 0`
     >- (irule (CONJUNCT1 zero_slot_size_slots_in_range) >> simp[type_slot_size_def]) >>
     `off + type_slot_size_list pre + type_slot_size tv < dimword(:256)` by decide_tac >>
     irule typed_write_storage_slot_preserves_disjoint_num_region >>
     asm_simp_tac bool_ss [] >>
     qexistsl_tac [`b`,`slot`,`st`,`leaf`,`v`] >>
     asm_simp_tac bool_ss [slots_in_range_tuple] >>
     simp_tac bool_ss [ranges_disjoint_def, type_slot_size_def] >> decide_tac) >>
  full_simp_tac bool_ss
    [slots_in_range_tuple, tuple_storage_regions_append,
     tuple_storage_region_equations, type_slot_size_def, ADD_ASSOC]
QED

Theorem fixed_storage_region[local]:
  slots_in_range storage off (ArrayTV tv (Fixed n)) <=>
  static_slots_in_range storage off tv n
Proof
  pure_once_rewrite_tac [slots_in_range_def] >> simp[]
QED

Theorem array_storage_list_equations[local]:
  static_slots_in_range storage off tv 0 = T /\
  (static_slots_in_range storage off tv (SUC n) <=>
    slots_in_range storage off tv /\
    static_slots_in_range storage (off + type_slot_size tv) tv n) /\
  dyn_slots_in_range storage off tv 0 = T /\
  (dyn_slots_in_range storage off tv (SUC n) <=>
    slots_in_range storage off tv /\
    dyn_slots_in_range storage (off + type_slot_size tv) tv n)
Proof
  rpt conj_tac >> pure_once_rewrite_tac [slots_in_range_def] >> simp[]
QED

Theorem dynamic_static_storage_regions:
  !n storage off tv. dyn_slots_in_range storage off tv n <=>
    static_slots_in_range storage off tv n
Proof
  Induct >> asm_simp_tac bool_ss [array_storage_list_equations]
QED

Theorem dynamic_storage_region[local]:
  slots_in_range storage off (ArrayTV tv (Dynamic max)) <=>
  w2n (read_slot storage off) <= max /\
  dyn_slots_in_range storage (off + 1) tv (w2n (read_slot storage off))
Proof
  pure_once_rewrite_tac [slots_in_range_def] >>
  simp_tac bool_ss [LET_THM] >>
  qabbrev_tac `len = w2n (read_slot storage off)` >>
  Cases_on `len <= max` >> asm_simp_tac bool_ss [] >>
  `MIN len max = len` by (simp[MIN_DEF] >> decide_tac) >>
  asm_simp_tac bool_ss []
QED

Theorem dynamic_dead_child_typed_write_reconstruct:
  slots_in_range (get_storage cx st b) off (ArrayTV tv (Dynamic max)) /\
  w2n (read_slot (get_storage cx st b) off) <= i /\ i < max /\
  0 < type_slot_size tv /\
  off + type_slot_size (ArrayTV tv (Dynamic max)) <= dimword(:256) /\
  off + 1 + i * type_slot_size tv <= w2n slot /\
  w2n slot + type_slot_size leaf <=
    off + 1 + (i * type_slot_size tv + type_slot_size tv) /\
  value_has_type leaf v /\
  write_storage_slot cx b slot leaf v st = (INL (),st') ==>
  slots_in_range (get_storage cx st' b) off (ArrayTV tv (Dynamic max))
Proof
  rpt strip_tac >>
  qpat_x_assum `slots_in_range (get_storage cx st b) off (ArrayTV tv (Dynamic max))`
    (strip_assume_tac o SIMP_RULE bool_ss [dynamic_storage_region]) >>
  qabbrev_tac `len = w2n (read_slot (get_storage cx st b) off)` >>
  `i * type_slot_size tv + type_slot_size tv <= max * type_slot_size tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  `off + 1 + max * type_slot_size tv <= dimword(:256)` by
    (qpat_x_assum `off + type_slot_size (ArrayTV tv (Dynamic max)) <= _` mp_tac >>
     simp_tac bool_ss [type_slot_size_def, ADD_ASSOC]) >>
  `off + 1 < dimword(:256)` by decide_tac >>
  `ranges_disjoint (w2n slot) (type_slot_size leaf) off 1` by
    (simp_tac bool_ss [ranges_disjoint_def] >> decide_tac) >>
  `read_slot (get_storage cx st' b) off = read_slot (get_storage cx st b) off` by
    (drule_all typed_write_storage_slot_preserves_disjoint_read_slot >> simp[]) >>
  `slots_in_range (get_storage cx st b) (off + 1) (ArrayTV tv (Fixed len))` by
    (pure_once_rewrite_tac [slots_in_range_def] >>
     asm_simp_tac bool_ss [GSYM dynamic_static_storage_regions]) >>
  `len * type_slot_size tv <= i * type_slot_size tv` by simp[LESS_MONO_MULT] >>
  `slots_in_range (get_storage cx st' b) (off + 1) (ArrayTV tv (Fixed len))` by
    (irule typed_write_storage_slot_preserves_disjoint_num_region >>
     asm_simp_tac bool_ss [] >>
     qexistsl_tac [`b`,`slot`,`st`,`leaf`,`v`] >>
     asm_simp_tac bool_ss [] >>
     simp_tac bool_ss [ranges_disjoint_def, type_slot_size_def] >> decide_tac) >>
  full_simp_tac bool_ss
    [dynamic_storage_region, fixed_storage_region,
     dynamic_static_storage_regions, Abbr`len`]
QED

Theorem tuple_component_storage_region:
  slots_in_range storage off (TupleTV (pre ++ tv::post)) ==>
  slots_in_range storage (off + type_slot_size_list pre) tv
Proof
  simp_tac bool_ss
    [slots_in_range_tuple, tuple_storage_regions_append, tuple_storage_region_equations] >>
  rpt strip_tac >> first_assum ACCEPT_TAC
QED

Theorem slots_in_range_struct[local]:
  slots_in_range storage off (StructTV fields) <=>
  slots_in_range storage off (TupleTV (MAP SND fields))
Proof
  pure_once_rewrite_tac [slots_in_range_def] >>
  simp_tac bool_ss [slots_in_range_tuple, struct_storage_regions_tuple]
QED

Theorem struct_component_region_split:
  struct_field_slot fields id = SOME (delta,elem) ==>
  ?pre post. MAP SND fields = pre ++ elem::post /\
    delta = type_slot_size_list pre
Proof
  strip_tac >> drule vyperPlaceTypingTheory.struct_field_slot_offset >> strip_tac >>
  qmatch_assum_rename_tac `fields = prefix_fields ++ (id,elem)::suffix_fields` >>
  qexistsl_tac [`MAP SND prefix_fields`,`MAP SND suffix_fields`] >>
  asm_simp_tac bool_ss [MAP_APPEND, MAP, SND, type_slot_size_list_sum, MAP_MAP_o]
QED

Theorem storage_subregion_typed_write_preserves_root:
  !tv path relative leaf.
    storage_subregion tv path relative leaf ==>
    !cx b off slot v st st'.
      well_formed_type_value leaf /\ 0 < type_slot_size leaf /\
      off + type_slot_size tv <= dimword(:256) /\
      w2n slot = off + relative /\
      slots_in_range (get_storage cx st b) off tv /\
      value_has_type leaf v /\
      write_storage_slot cx b slot leaf v st = (INL (),st') ==>
      slots_in_range (get_storage cx st' b) off tv
Proof
  ho_match_mp_tac storage_subregion_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >>
  FIRST [
    qpat_x_assum `storage_subregion _ [] _ _` mp_tac >>
      simp_tac (srw_ss()) [Once storage_subregion_def] >> strip_tac >> gvs[] >>
      drule_all typed_write_storage_slot_establishes_region >> simp[],
    qpat_x_assum `storage_subregion _ (_::_) _ _` mp_tac >>
      simp_tac (srw_ss()) [Once storage_subregion_def] >> strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      FIRST [rename1 `slots_in_range _ _ (ArrayTV _ (Fixed _))` >> suspend "Fixed",
             rename1 `slots_in_range _ _ (ArrayTV _ (Dynamic _))` >> suspend "Dynamic",
             rename1 `slots_in_range _ _ (StructTV _)` >> suspend "Struct",
             rename1 `slots_in_range _ _ (TupleTV _)` >> suspend "Tuple"]]
QED

Resume storage_subregion_typed_write_preserves_root[Fixed]:
  RESUME_TAC >> drule_all storage_subregion_bounds >> strip_tac >>
  `0 < type_slot_size tv` by decide_tac >>
  `Num i * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  `off + Num i * type_slot_size tv + type_slot_size tv <= dimword(:256)` by
    (qpat_assum `off + type_slot_size (ArrayTV tv (Fixed n)) <= _` mp_tac >>
     simp_tac bool_ss [type_slot_size_def] >> strip_tac >> decide_tac) >>
  `slots_in_range (get_storage cx st b) (off + Num i * type_slot_size tv) tv` by
    (irule static_slots_in_range_index >> qexists_tac `n` >>
     asm_simp_tac bool_ss [GSYM fixed_storage_region]) >>
  qpat_x_assum `!relative. storage_subregion tv path relative leaf ==> _`
    (qspec_then `rest` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then
    [`cx`,`b`,`off + Num i * type_slot_size tv`,`slot`,`v`,`st`,`st'`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac)) >> strip_tac >>
  irule fixed_array_typed_leaf_write_reconstruct >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`leaf`,`Num i`,`slot`,`st`,`v`] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Resume storage_subregion_typed_write_preserves_root[Dynamic]:
  RESUME_TAC >> drule_all storage_subregion_bounds >> strip_tac >>
  `0 < type_slot_size tv` by decide_tac >>
  `Num i * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  `off + 1 + Num i * type_slot_size tv + type_slot_size tv <= dimword(:256)` by
    (qpat_assum `off + type_slot_size (ArrayTV tv (Dynamic n)) <= _` mp_tac >>
     simp_tac bool_ss [type_slot_size_def, ADD_ASSOC] >> strip_tac >> decide_tac) >>
  Cases_on `Num i < w2n (read_slot (get_storage cx st b) off)`
  >- (qpat_assum `slots_in_range (get_storage cx st b) off (ArrayTV tv (Dynamic n))`
        (strip_assume_tac o SIMP_RULE bool_ss [dynamic_storage_region]) >>
      `slots_in_range (get_storage cx st b) (off + 1 + Num i * type_slot_size tv) tv` by
        (irule dyn_slots_in_range_index >>
         qexists_tac `w2n (read_slot (get_storage cx st b) off)` >>
         asm_simp_tac bool_ss []) >>
      qpat_x_assum `!relative. storage_subregion tv path relative leaf ==> _`
        (qspec_then `rest` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (qspecl_then
        [`cx`,`b`,`off + 1 + Num i * type_slot_size tv`,`slot`,`v`,`st`,`st'`] mp_tac) >>
      (impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac)) >> strip_tac >>
      irule dynamic_array_typed_leaf_write_reconstruct >> asm_simp_tac bool_ss [] >>
      qexistsl_tac [`leaf`,`Num i`,`slot`,`st`,`v`] >>
      asm_simp_tac bool_ss [] >> decide_tac) >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  irule dynamic_dead_child_typed_write_reconstruct >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`Num i`,`leaf`,`slot`,`st`,`v`] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Resume storage_subregion_typed_write_preserves_root[Struct]:
  RESUME_TAC >> drule struct_component_region_split >> strip_tac >>
  qmatch_assum_rename_tac `MAP SND fields = prefix_types ++ elem::suffix_types` >>
  qpat_x_assum `delta = type_slot_size_list prefix_types` SUBST_ALL_TAC >>
  drule_all storage_subregion_bounds >> strip_tac >>
  `0 < type_slot_size elem` by decide_tac >>
  `slots_in_range (get_storage cx st b) off
     (TupleTV (prefix_types ++ elem::suffix_types))` by
    (qpat_assum `slots_in_range (get_storage cx st b) off (StructTV fields)`
       (mp_tac o REWRITE_RULE [slots_in_range_struct]) >>
     asm_simp_tac bool_ss []) >>
  `off + type_slot_size (TupleTV (prefix_types ++ elem::suffix_types)) <= dimword(:256)` by
    (qpat_assum `off + type_slot_size (StructTV fields) <= _`
       (mp_tac o REWRITE_RULE [type_slot_size_def, type_slot_size_fields_list]) >>
     asm_simp_tac bool_ss [type_slot_size_def]) >>
  `off + type_slot_size_list prefix_types + type_slot_size elem <= dimword(:256)` by
    (qpat_assum `off + type_slot_size (TupleTV (prefix_types ++ elem::suffix_types)) <= _`
       mp_tac >>
     simp_tac bool_ss [type_slot_size_def, type_slot_size_list_append, ADD_ASSOC] >>
     strip_tac >> decide_tac) >>
  `slots_in_range (get_storage cx st b) (off + type_slot_size_list prefix_types) elem` by
    (drule tuple_component_storage_region >> simp[]) >>
  qpat_x_assum `!tv relative. storage_subregion tv path relative leaf ==> _`
    (qspecl_then [`elem`,`rest`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then
    [`cx`,`b`,`off + type_slot_size_list prefix_types`,`slot`,`v`,`st`,`st'`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac)) >> strip_tac >>
  pure_once_rewrite_tac [slots_in_range_struct] >> asm_simp_tac bool_ss [] >>
  irule tuple_component_typed_write_reconstruct >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`leaf`,`slot`,`st`,`v`] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Resume storage_subregion_typed_write_preserves_root[Tuple]:
  RESUME_TAC >> drule tuple_component_region_split >> strip_tac >>
  qmatch_assum_rename_tac `types = prefix_types ++ elem::suffix_types` >>
  qpat_x_assum `types = prefix_types ++ elem::suffix_types` SUBST_ALL_TAC >>
  qpat_x_assum `tuple_prefix_slot_size _ _ = _` SUBST_ALL_TAC >>
  drule_all storage_subregion_bounds >> strip_tac >>
  `0 < type_slot_size elem` by decide_tac >>
  `off + type_slot_size_list prefix_types + type_slot_size elem <= dimword(:256)` by
    (qpat_assum `off + type_slot_size (TupleTV (prefix_types ++ elem::suffix_types)) <= _`
       mp_tac >>
     simp_tac bool_ss [type_slot_size_def, type_slot_size_list_append, ADD_ASSOC] >>
     strip_tac >> decide_tac) >>
  `slots_in_range (get_storage cx st b) (off + type_slot_size_list prefix_types) elem` by
    (drule tuple_component_storage_region >> simp[]) >>
  qpat_x_assum `!tv relative. storage_subregion tv path relative leaf ==> _`
    (qspecl_then [`elem`,`rest`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then
    [`cx`,`b`,`off + type_slot_size_list prefix_types`,`slot`,`v`,`st`,`st'`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac)) >> strip_tac >>
  irule tuple_component_typed_write_reconstruct >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`leaf`,`slot`,`st`,`v`] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Finalise storage_subregion_typed_write_preserves_root
val _ = if null (hyp storage_subregion_typed_write_preserves_root) then ()
  else raise Fail "Storage-region write theorem retains suspension hypotheses";
