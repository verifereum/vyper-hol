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

(* Storage validity depends only on reads inside the capacity interval. *)
Theorem storage_interval_congruence_mutual:
  (!s off tv. !s'.
    off + type_slot_size tv <= dimword(:256) /\
    slots_in_range s off tv /\
    (!a. off <= a /\ a < off + type_slot_size tv ==>
      read_slot s' a = read_slot s a) ==>
    slots_in_range s' off tv) /\
  (!s off tvs. !s'.
    off + type_slot_size_list tvs <= dimword(:256) /\
    tuple_slots_in_range s off tvs /\
    (!a. off <= a /\ a < off + type_slot_size_list tvs ==>
      read_slot s' a = read_slot s a) ==>
    tuple_slots_in_range s' off tvs) /\
  (!s off tv n. !s'.
    off + n * type_slot_size tv <= dimword(:256) /\
    static_slots_in_range s off tv n /\
    (!a. off <= a /\ a < off + n * type_slot_size tv ==>
      read_slot s' a = read_slot s a) ==>
    static_slots_in_range s' off tv n) /\
  (!s off tv n. !s'.
    off + n * type_slot_size tv <= dimword(:256) /\
    dyn_slots_in_range s off tv n /\
    (!a. off <= a /\ a < off + n * type_slot_size tv ==>
      read_slot s' a = read_slot s a) ==>
    dyn_slots_in_range s' off tv n) /\
  (!s off fields. !s'.
    off + type_slot_size_fields fields <= dimword(:256) /\
    struct_slots_in_range s off fields /\
    (!a. off <= a /\ a < off + type_slot_size_fields fields ==>
      read_slot s' a = read_slot s a) ==>
    struct_slots_in_range s' off fields)
Proof
  ho_match_mp_tac slots_in_range_ind >>
  rpt conj_tac >> rpt gen_tac >>
  PURE_ONCE_REWRITE_TAC [slots_in_range_def] >>
  simp_tac (srw_ss()) [type_slot_size_def, LET_THM] >>
  rpt strip_tac >> gvs[]
  >- (`type_slot_size tv * MIN (w2n (read_slot s off)) max <=
         max * type_slot_size tv` by (simp[MIN_DEF] >> IF_CASES_TAC >>
            simp[] >> metis_tac[LESS_MONO_MULT, MULT_COMM]) >>
      first_x_assum irule >> conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      decide_tac) >>
  gvs[MULT_CLAUSES] >> first_assum irule
QED

Theorem tuple_component_storage_transport:
  off + type_slot_size_list (pre ++ tv::post) <= dimword(:256) /\
  tuple_slots_in_range s off (pre ++ tv::post) /\
  slots_in_range s' (off + type_slot_size_list pre) tv /\
  (!a. a < dimword(:256) /\
       (a < off + type_slot_size_list pre \/
        off + type_slot_size_list pre + type_slot_size tv <= a) ==>
       read_slot s' a = read_slot s a) ==>
  tuple_slots_in_range s' off (pre ++ tv::post)
Proof
  simp_tac bool_ss [tuple_storage_regions_append,
    tuple_storage_region_equations, type_slot_size_list_append,
    type_slot_size_def, ADD_ASSOC] >> strip_tac >>
  conj_tac
  >- (irule (cj 2 storage_interval_congruence_mutual) >>
      conj_tac >- decide_tac >> qexists `s` >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  irule (cj 2 storage_interval_congruence_mutual) >>
  conj_tac >- decide_tac >> qexists `s` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem static_prefix_storage_transport:
  off + n * type_slot_size tv <= dimword(:256) /\
  static_slots_in_range s off tv n /\
  (i < n ==> slots_in_range s' (off + i * type_slot_size tv) tv) /\
  (!a. a < dimword(:256) /\
       (a < off + i * type_slot_size tv \/
        off + i * type_slot_size tv + type_slot_size tv <= a) ==>
       read_slot s' a = read_slot s a) ==>
  static_slots_in_range s' off tv n
Proof
  strip_tac >> irule static_slots_in_range_reconstruct >>
  rpt strip_tac >> Cases_on `j = i` >- gvs[] >>
  `j * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv`
    by (irule array_index_element_end_bound >> simp[]) >>
  `slots_in_range s (off + j * type_slot_size tv) tv`
    by (irule static_slots_in_range_index >> qexists `n` >> simp[]) >>
  irule (cj 1 storage_interval_congruence_mutual) >>
  conj_tac >- decide_tac >> qexists `s` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> conj_tac >- decide_tac >>
  Cases_on `j < i`
  >- (`j * type_slot_size tv + type_slot_size tv <= i * type_slot_size tv`
        by (irule array_index_element_end_bound >> simp[]) >> decide_tac) >>
  `i * type_slot_size tv + type_slot_size tv <= j * type_slot_size tv`
    by (irule array_index_element_end_bound >> simp[]) >> decide_tac
QED

Theorem dynamic_child_storage_transport:
  off + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) /\
  slots_in_range s off (ArrayTV tv (Dynamic n)) /\
  (i < w2n (read_slot s off) ==>
     slots_in_range s' (off + 1 + i * type_slot_size tv) tv) /\
  (!a. a < dimword(:256) /\
       (a < off + 1 + i * type_slot_size tv \/
        off + 1 + i * type_slot_size tv + type_slot_size tv <= a) ==>
       read_slot s' a = read_slot s a) ==>
  slots_in_range s' off (ArrayTV tv (Dynamic n))
Proof
  simp_tac bool_ss [dynamic_storage_region, dynamic_static_storage_regions,
    type_slot_size_def] >> strip_tac >>
  `read_slot s' off = read_slot s off` by
    (first_x_assum irule >> decide_tac) >> simp[] >>
  irule static_prefix_storage_transport >> conj_tac
  >- (`w2n (read_slot s off) * type_slot_size tv <= n * type_slot_size tv`
        by metis_tac[LESS_MONO_MULT] >> decide_tac) >>
  qexistsl [`i`,`s`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem storage_subregion_transport:
  !root path delta leaf.
  storage_subregion root path delta leaf ==>
  !off s s'.
    0 < type_slot_size leaf /\
    off + type_slot_size root <= dimword(:256) /\
    slots_in_range s off root /\
    (!a. a < dimword(:256) /\
         (a < off + delta \/ off + delta + type_slot_size leaf <= a) ==>
         read_slot s' a = read_slot s a) /\
    (slots_in_range s (off + delta) leaf ==>
     slots_in_range s' (off + delta) leaf) ==>
    slots_in_range s' off root
Proof
  ho_match_mp_tac storage_subregion_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >>
  FIRST [
    qpat_x_assum `storage_subregion _ [] _ _` mp_tac >>
      simp_tac (srw_ss()) [Once storage_subregion_def] >> strip_tac >> gvs[],
    qpat_x_assum `storage_subregion _ (_::_) _ _` mp_tac >>
      simp_tac (srw_ss()) [Once storage_subregion_def] >> strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      FIRST [rename1 `slots_in_range _ _ (ArrayTV _ (Fixed _))` >> suspend "Fixed",
             rename1 `slots_in_range _ _ (ArrayTV _ (Dynamic _))` >> suspend "Dynamic",
             rename1 `slots_in_range _ _ (StructTV _)` >> suspend "Struct",
             rename1 `slots_in_range _ _ (TupleTV _)` >> suspend "Tuple"]]
QED

Resume storage_subregion_transport[Fixed]:
  RESUME_TAC >> drule_all storage_subregion_bounds >> strip_tac >>
  `Num i * type_slot_size root + type_slot_size root <= n * type_slot_size root`
    by (irule array_index_element_end_bound >> simp[]) >>
  gvs[fixed_storage_region, type_slot_size_def] >>
  irule static_prefix_storage_transport >> conj_tac
  >- simp[] >> qexistsl [`Num i`,`s`] >>
  simp_tac bool_ss [] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> gvs[] >> decide_tac) >>
  conj_tac >- (strip_tac >>
    qpat_x_assum `!delta. storage_subregion _ _ _ _ ==> _` drule >>
    disch_then irule >> conj_tac >- decide_tac >>
    qexists `s` >>
    rule_assum_tac (SIMP_RULE bool_ss [AC ADD_ASSOC ADD_COMM]) >>
    asm_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    irule static_slots_in_range_index >> qexists `n` >>
    asm_simp_tac bool_ss []) >> first_assum ACCEPT_TAC
QED

Resume storage_subregion_transport[Dynamic]:
  RESUME_TAC >> drule_all storage_subregion_bounds >> strip_tac >>
  `Num i * type_slot_size root + type_slot_size root <= n * type_slot_size root`
    by (irule array_index_element_end_bound >> simp[]) >>
  irule dynamic_child_storage_transport >> conj_tac
  >- first_assum ACCEPT_TAC >> qexistsl [`Num i`,`s`] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac >- (strip_tac >>
    qpat_x_assum `!delta. storage_subregion _ _ _ _ ==> _` drule >>
    disch_then irule >> conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac
    >- (qpat_x_assum `off + type_slot_size (ArrayTV _ _) <= _` mp_tac >>
        simp_tac bool_ss [type_slot_size_def] >> decide_tac) >>
    qexists `s` >>
    rule_assum_tac (SIMP_RULE bool_ss [AC ADD_ASSOC ADD_COMM]) >>
    asm_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    pure_rewrite_tac [ADD_ASSOC] >>
    irule dyn_slots_in_range_index >>
    qexists `w2n (read_slot s off)` >>
    qpat_x_assum `slots_in_range s off (ArrayTV _ _)` mp_tac >>
    asm_simp_tac bool_ss [dynamic_storage_region, ADD_ASSOC]) >>
  first_assum ACCEPT_TAC
QED

Resume storage_subregion_transport[Struct]:
  RESUME_TAC >> drule struct_component_region_split >> strip_tac >>
  qmatch_assum_rename_tac `MAP SND fields = pre ++ elem::post` >>
  qpat_x_assum `delta' = _` SUBST_ALL_TAC >>
  drule_all storage_subregion_bounds >> strip_tac >>
  full_simp_tac bool_ss [slots_in_range_struct, slots_in_range_tuple,
      type_slot_size_def, type_slot_size_fields_list,
      type_slot_size_list_append] >>
  irule tuple_component_storage_transport >> conj_tac
  >- (simp_tac bool_ss [type_slot_size_list_append, type_slot_size_def] >>
      decide_tac) >>
  conj_tac
  >- (qpat_x_assum `!root delta. storage_subregion _ _ _ _ ==> _` drule >>
      disch_then irule >> conj_tac >- decide_tac >> qexists `s` >>
      rule_assum_tac (SIMP_RULE bool_ss [AC ADD_ASSOC ADD_COMM]) >>
      asm_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `tuple_slots_in_range s off _` mp_tac >>
      simp_tac bool_ss [tuple_storage_regions_append, tuple_storage_region_equations] >>
      metis_tac[]) >>
  qexists `s` >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  first_assum ACCEPT_TAC
QED

Resume storage_subregion_transport[Tuple]:
  RESUME_TAC >> drule tuple_component_region_split >> strip_tac >>
  qmatch_assum_rename_tac `types = pre ++ elem::post` >>
  qpat_x_assum `types = _` SUBST_ALL_TAC >>
  qpat_x_assum `tuple_prefix_slot_size _ _ = _` SUBST_ALL_TAC >>
  drule_all storage_subregion_bounds >> strip_tac >>
  full_simp_tac bool_ss [slots_in_range_tuple, type_slot_size_def,
      type_slot_size_list_append] >>
  irule tuple_component_storage_transport >> conj_tac
  >- (simp_tac bool_ss [type_slot_size_list_append, type_slot_size_def] >>
      decide_tac) >>
  conj_tac
  >- (qpat_x_assum `!root delta. storage_subregion _ _ _ _ ==> _` drule >>
      disch_then irule >> conj_tac >- decide_tac >> qexists `s` >>
      rule_assum_tac (SIMP_RULE bool_ss [AC ADD_ASSOC ADD_COMM]) >>
      asm_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `tuple_slots_in_range s off _` mp_tac >>
      simp_tac bool_ss [tuple_storage_regions_append, tuple_storage_region_equations] >>
      metis_tac[]) >>
  qexists `s` >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  first_assum ACCEPT_TAC
QED

Finalise storage_subregion_transport

Theorem base_storage_write_footprint:
  write_storage_slot cx tr slot (BaseTV (UintT 256)) v st = (res,st') ==>
  get_storage cx st' (~tr) = get_storage cx st (~tr) /\
  (!a. a < dimword(:256) /\ a <> w2n slot ==>
     read_slot (get_storage cx st' tr) a = read_slot (get_storage cx st tr) a)
Proof
  simp_tac bool_ss [write_storage_slot_eq, vyperStorageTheory.encode_value_def] >>
  Cases_on `encode_base_to_slot v (BaseTV (UintT 256))` >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
  Cases_on `tr` >>
  simp[get_storage_after_set, get_storage_after_set_other, vyperStorageTheory.apply_writes_def] >>
  rpt strip_tac >>
  simp[vyperStorageTheory.read_slot_def, vfmStateTheory.lookup_storage_def,
       vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  `n2w a <> (slot:bytes32)` by
    (strip_tac >> `w2n (n2w a : bytes32) = w2n slot` by simp[] >> gvs[]) >>
  simp[]
QED

Theorem storage_pop_footprint:
  w2n slot + type_slot_size (ArrayTV etv (Dynamic n)) <= dimword(:256) /\
  pop_place cx (StoragePlace tr slot (ArrayTV etv (Dynamic n))) st = (res,st') ==>
  get_storage cx st' (~tr) = get_storage cx st (~tr) /\
  (!a. a < dimword(:256) /\
       (a < w2n slot \/ w2n slot + type_slot_size (ArrayTV etv (Dynamic n)) <= a) ==>
     read_slot (get_storage cx st' tr) a = read_slot (get_storage cx st tr) a)
Proof
  simp_tac bool_ss [pop_place_def, get_storage_backend_eq, bind_def,
    ignore_bind_def, check_def, assert_def, return_def, raise_def, LET_THM] >>
  Cases_on `0 < w2n (lookup_storage slot (get_storage cx st tr))` >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
  Cases_on `write_storage_slot cx tr slot (BaseTV (UintT 256))
      (IntV (&(w2n (lookup_storage slot (get_storage cx st tr)) - 1))) st` >>
  Cases_on `q` >> gvs[] >>
  drule base_storage_write_footprint >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  gvs[type_slot_size_def] >> decide_tac
QED

Theorem typed_zero_storage_write_footprint:
  type_slot_size tv = 0 /\ value_has_type tv v /\
  write_storage_slot cx tr slot tv v st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  strip_tac >> gvs[write_storage_slot_eq, AllCaseEqs()] >>
  drule (CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
  simp[] >> strip_tac >>
  `writes = []` by
    (Cases_on `writes` >> gvs[] >> PairCases_on `h` >>
     first_x_assum (qspec_then `h0` mp_tac) >> simp[]) >>
  gvs[vyperStorageTheory.apply_writes_def] >>
  Cases >> Cases_on `tr` >>
  simp[get_storage_after_set, get_storage_after_set_other]
QED

Theorem storage_write_other_backend:
  write_storage_slot cx tr slot tv v st = (res,st') ==>
  get_storage cx st' (~tr) = get_storage cx st (~tr)
Proof
  strip_tac >> gvs[write_storage_slot_eq, AllCaseEqs()] >>
  Cases_on `tr` >> simp[get_storage_after_set_other]
QED

Theorem storage_append_element_footprint:
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) /\
  len < n /\ value_has_type tv v /\
  write_storage_slot cx tr (slot + n2w (1 + len * type_slot_size tv)) tv v st = (res,st') ==>
  !a. a < dimword(:256) /\
       (a < w2n slot \/ w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= a) ==>
    read_slot (get_storage cx st' tr) a = read_slot (get_storage cx st tr) a
Proof
  strip_tac >> Cases_on `type_slot_size tv = 0`
  >- (drule_all typed_zero_storage_write_footprint >> simp[]) >>
  `0 < type_slot_size tv` by decide_tac >>
  `w2n (slot + n2w (1 + len * type_slot_size tv)) =
     w2n slot + 1 + len * type_slot_size tv` by
    (drule_all dynamic_array_child_region_bounds >> simp[]) >>
  `len * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv`
    by (irule array_index_element_end_bound >> simp[]) >>
  Cases_on `res`
  >- (Cases_on `x` >> rpt strip_tac >>
      drule typed_write_storage_slot_preserves_disjoint_read_slot >>
      disch_then drule >> disch_then irule >>
      simp[ranges_disjoint_def, type_slot_size_def] >>
      gvs[type_slot_size_def] >> decide_tac) >>
  gvs[write_storage_slot_eq, AllCaseEqs()]
QED

Theorem storage_append_element_read_frame:
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) /\
  len < n /\ value_has_type tv v /\
  write_storage_slot cx tr (slot + n2w (1 + len * type_slot_size tv)) tv v st = (res,st') /\
  a < dimword(:256) /\
  (a < w2n slot \/ w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= a) ==>
  read_slot (get_storage cx st' tr) a = read_slot (get_storage cx st tr) a
Proof
  metis_tac[storage_append_element_footprint]
QED

Theorem storage_append_footprint:
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) /\
  value_has_type tv v /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) v st = (res,st') ==>
  get_storage cx st' (~tr) = get_storage cx st (~tr) /\
  (!a. a < dimword(:256) /\
       (a < w2n slot \/ w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= a) ==>
     read_slot (get_storage cx st' tr) a = read_slot (get_storage cx st tr) a)
Proof
  simp_tac bool_ss [append_place_def, get_storage_backend_eq, bind_def,
    ignore_bind_def, check_def, assert_def, return_def, raise_def, LET_THM] >>
  Cases_on `w2n (lookup_storage slot (get_storage cx st tr)) < n` >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
  Cases_on `write_storage_slot cx tr
    (slot + n2w (1 + w2n (lookup_storage slot (get_storage cx st tr)) * type_slot_size tv))
    tv v st` >> Cases_on `q` >> gvs[]
  >- (drule base_storage_write_footprint >> strip_tac >>
      conj_tac
      >- metis_tac[storage_write_other_backend] >>
      rpt strip_tac >> (
      `a <> w2n slot` by (gvs[type_slot_size_def] >> decide_tac) >>
      `read_slot (get_storage cx st' tr) a = read_slot (get_storage cx r tr) a`
        by (first_x_assum irule >> simp[]) >>
      simp[] >> irule storage_append_element_read_frame >>
      conj_tac >- simp[] >>
      qexists `w2n (lookup_storage slot (get_storage cx st tr))` >>
      qexists `n` >> qexists `INL ()` >>
      qexists `slot` >> qexists `tv` >> qexists `v` >>
      qpat_x_assum `!a. _` kall_tac >>
      qpat_x_assum `read_slot _ _ = _` kall_tac >>
      full_simp_tac (srw_ss()) [ADD_COMM, MULT_COMM])) >>
  conj_tac >- metis_tac[storage_write_other_backend] >>
  rpt strip_tac >> (
  irule storage_append_element_read_frame >>
  conj_tac >- simp[] >>
  qexists `w2n (lookup_storage slot (get_storage cx st tr))` >>
  qexists `n` >> qexists `INR y` >>
  qexists `slot` >> qexists `tv` >> qexists `v` >>
  full_simp_tac (srw_ss()) [ADD_COMM, MULT_COMM])
QED

Theorem zero_width_dynamic_storage_prefix:
  type_slot_size etv = 0 ==> dyn_slots_in_range storage off etv k
Proof
  strip_tac >> irule dyn_slots_in_range_reconstruct >> rpt strip_tac >>
  irule (CONJUNCT1 zero_slot_size_slots_in_range) >> simp[]
QED

Theorem zero_width_dynamic_storage_region:
  type_slot_size etv = 0 ==>
  (slots_in_range storage off (ArrayTV etv (Dynamic n)) <=>
   w2n (read_slot storage off) <= n)
Proof
  strip_tac >> simp[Once slots_in_range_def, zero_width_dynamic_storage_prefix]
QED

Theorem zero_width_header_write_preserves_array:
  type_slot_size etv = 0 /\ len <= n /\ len < dimword(:256) /\
  write_storage_slot cx b (n2w off) (BaseTV (UintT 256)) (IntV (&len)) st =
    (INL (),st') ==>
  slots_in_range (get_storage cx st' b) off (ArrayTV etv (Dynamic n))
Proof
  strip_tac >> simp[zero_width_dynamic_storage_region] >>
  drule_all uint256_header_write_read_exact >> simp[]
QED

Theorem storage_pop_preserves_array:
  well_formed_type_value (ArrayTV tv (Dynamic n)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) /\
  slots_in_range (get_storage cx st tr) (w2n slot) (ArrayTV tv (Dynamic n)) /\
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) st = (res,st') ==>
  slots_in_range (get_storage cx st' tr) (w2n slot) (ArrayTV tv (Dynamic n))
Proof
  simp_tac bool_ss [pop_place_def, get_storage_backend_eq, bind_def,
    ignore_bind_def, check_def, assert_def, return_def, raise_def, LET_THM] >>
  Cases_on `0 < w2n (lookup_storage slot (get_storage cx st tr))` >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
  Cases_on `write_storage_slot cx tr slot (BaseTV (UintT 256))
      (IntV (&(w2n (lookup_storage slot (get_storage cx st tr)) - 1))) st` >>
  Cases_on `q` >> gvs[]
  >- (Cases_on `type_slot_size tv = 0`
      >- (irule zero_width_header_write_preserves_array >>
          conj_tac >- first_assum ACCEPT_TAC >> qexists `w2n (lookup_storage slot (get_storage cx st tr)) - 1` >>
          qexists `st` >> simp[] >>
          qpat_x_assum `slots_in_range _ _ _` mp_tac >>
          simp[zero_width_dynamic_storage_region, vyperStorageTheory.read_slot_def] >>
          assume_tac (wordsTheory.w2n_lt |> Q.ISPEC `lookup_storage slot (get_storage cx st tr)`) >>
          gvs[dimword_def] >> decide_tac) >>
      irule dynamic_array_pop_header_write_preserves >>
      conj_tac >- decide_tac >> conj_tac >- simp[] >> qexists `w2n (lookup_storage slot (get_storage cx st tr))` >>
      qexists `st` >> simp[vyperStorageTheory.read_slot_def]) >>
  gvs[write_storage_slot_eq, AllCaseEqs()]
QED

Theorem storage_append_preserves_array:
  well_formed_type_value (ArrayTV tv (Dynamic n)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) /\
  slots_in_range (get_storage cx st tr) (w2n slot) (ArrayTV tv (Dynamic n)) /\
  value_has_type tv v /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) v st = (res,st') ==>
  slots_in_range (get_storage cx st' tr) (w2n slot) (ArrayTV tv (Dynamic n))
Proof
  simp_tac bool_ss [append_place_def, get_storage_backend_eq, bind_def,
    ignore_bind_def, check_def, assert_def, return_def, raise_def, LET_THM] >>
  Cases_on `w2n (lookup_storage slot (get_storage cx st tr)) < n` >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
  Cases_on `write_storage_slot cx tr
    (slot + n2w (1 + w2n (lookup_storage slot (get_storage cx st tr)) * type_slot_size tv))
    tv v st` >> Cases_on `q` >> gvs[]
  >- (Cases_on `type_slot_size tv = 0`
      >- suspend "zero_width" >> suspend "positive_width") >>
  gvs[write_storage_slot_eq, AllCaseEqs()]
QED

Resume storage_append_preserves_array[zero_width]:
  RESUME_TAC >>
  drule_all typed_zero_storage_write_footprint >> strip_tac >>
  Cases_on `res` >> gvs[]
  >- (gvs[write_storage_slot_eq, vyperStorageTheory.encode_value_def,
           vyperStorageTheory.encode_base_to_slot_def] >>
      simp[zero_width_dynamic_storage_region, get_storage_after_set,
           vyperStorageTheory.read_slot_def, vyperStorageTheory.apply_writes_def,
           vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
           combinTheory.APPLY_UPDATE_THM, integer_wordTheory.i2w_pos] >>
      irule arithmeticTheory.LESS_EQ_TRANS >>
      qexists `w2n (get_storage cx st tr slot) + 1` >> conj_tac
      >- (irule arithmeticTheory.MOD_LESS_EQ >> simp[]) >>
      gvs[vfmStateTheory.lookup_storage_def]) >>
  gvs[write_storage_slot_eq, AllCaseEqs()]
QED

Resume storage_append_preserves_array[positive_width]:
  RESUME_TAC >>
  `0 < type_slot_size tv` by decide_tac >>
  `n <= n * type_slot_size tv` by
    (once_rewrite_tac [GSYM arithmeticTheory.LE_MULT_CANCEL_LBARE] >> simp[]) >>
  `n < dimword(:256)` by
    (qpat_x_assum `n <= n * type_slot_size tv` mp_tac >>
     qpat_x_assum `type_slot_size _ + _ <= _` mp_tac >>
     pure_rewrite_tac [type_slot_size_def] >>
     qmatch_goalsub_abbrev_tac `n < d` >>
     `d = 115792089237316195423570985008687907853269984665640564039457584007913129639936` by
       simp[Abbr `d`] >> pop_assum SUBST_ALL_TAC >> decide_tac) >>
  `well_formed_type_value tv` by gvs[well_formed_type_value_def] >>
  `slot + n2w (type_slot_size tv * w2n (lookup_storage slot (get_storage cx st tr)) + 1) =
   n2w (w2n slot + 1 + w2n (lookup_storage slot (get_storage cx st tr)) * type_slot_size tv)` by
    simp_tac bool_ss [GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n,
      AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM, MULT_COMM] >>
  gvs[] >> Cases_on `res` >> gvs[]
  >- (irule dynamic_array_append_two_writes_preserve_v2 >>
      simp[] >>
      qexistsl [`st`, `r`, `v`] >>
      full_simp_tac (srw_ss()) [vyperStorageTheory.read_slot_def, MULT_COMM,
        AC ADD_ASSOC ADD_COMM]) >>
  gvs[write_storage_slot_eq, AllCaseEqs(), vyperStorageTheory.encode_value_def,
      vyperStorageTheory.encode_base_to_slot_def]
QED

Finalise storage_append_preserves_array

Theorem storage_subregion_append_preserves_root:
  storage_subregion root path delta (ArrayTV etv (Dynamic n)) /\
  well_formed_type_value (ArrayTV etv (Dynamic n)) /\
  off + type_slot_size root <= dimword(:256) /\
  w2n slot = off + delta /\
  slots_in_range (get_storage cx st tr) off root /\
  value_has_type etv v /\
  append_place cx (StoragePlace tr slot (ArrayTV etv (Dynamic n))) v st = (res,st') ==>
  slots_in_range (get_storage cx st' tr) off root
Proof
  strip_tac >> drule storage_subregion_bounds >> strip_tac >>
  `w2n slot + type_slot_size (ArrayTV etv (Dynamic n)) <= dimword(:256)` by decide_tac >>
  drule_all storage_append_footprint >> strip_tac >>
  drule storage_subregion_transport >> disch_then irule >>
  conj_tac >- simp[type_slot_size_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `get_storage cx st tr` >> conj_tac
  >- metis_tac[] >> conj_tac
  >- (strip_tac >> metis_tac[storage_append_preserves_array]) >>
  first_assum ACCEPT_TAC
QED

Theorem storage_subregion_pop_preserves_root:
  storage_subregion root path delta (ArrayTV etv (Dynamic n)) /\
  well_formed_type_value (ArrayTV etv (Dynamic n)) /\
  off + type_slot_size root <= dimword(:256) /\
  w2n slot = off + delta /\
  slots_in_range (get_storage cx st tr) off root /\
  pop_place cx (StoragePlace tr slot (ArrayTV etv (Dynamic n))) st = (res,st') ==>
  slots_in_range (get_storage cx st' tr) off root
Proof
  strip_tac >> drule storage_subregion_bounds >> strip_tac >>
  `w2n slot + type_slot_size (ArrayTV etv (Dynamic n)) <= dimword(:256)` by decide_tac >>
  drule_all storage_pop_footprint >> strip_tac >>
  drule storage_subregion_transport >> disch_then irule >>
  conj_tac >- simp[type_slot_size_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `get_storage cx st tr` >> conj_tac
  >- metis_tac[] >> conj_tac
  >- (strip_tac >> metis_tac[storage_pop_preserves_array]) >>
  first_assum ACCEPT_TAC
QED
