(* Typed tuple offsets for the linked subscript endpoint. *)
Theory bodySubscriptTupleGeometryMods
Ancestors
  exprSimTuple exprSimAttributeFields exprSimFieldLayout tupleMemoryLayout
  loweringPosts compileEnv vyperState vyperTypeABI vyperValue
  valueEncoding valueEncodingProofs vyperStorageRegionWrite list

Theorem tuple_subscript_geometry_mods:
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  k < LENGTH tys /\
  (!ty rt. evaluate_type (get_tenv cx) ty = SOME rt ==>
           type_memory_bytes cenv ty = type_memory_size rt) ==>
  k < LENGTH tvs /\
  evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs) /\
  type_memory_bytes cenv (EL k tys) = type_memory_size (EL k tvs) /\
  tuple_offset cenv tys LocMemory k = SUM (MAP type_memory_size (TAKE k tvs)) /\
  tuple_offset cenv tys LocCode k = SUM (MAP type_memory_size (TAKE k tvs)) /\
  (!tr. tuple_offset cenv tys (slot_loc tr) k = tuple_prefix_slot_size k tvs) /\
  SUM (MAP type_memory_size (TAKE k tvs)) + type_memory_size (EL k tvs) <=
    type_memory_size (TupleTV tvs) /\
  tuple_prefix_slot_size k tvs + type_slot_size (EL k tvs) <=
    type_slot_size (TupleTV tvs) /\
  mem_step_offset (TupleTV tvs) (ValueSubscript (IntV (&k))) =
    SOME (SUM (MAP type_memory_size (TAKE k tvs)), EL k tvs)
Proof
  strip_tac >> drule_then assume_tac OPT_MMAP_LENGTH >>
  `!j. j < LENGTH tys ==>
       evaluate_type (get_tenv cx) (EL j tys) = SOME (EL j tvs)` by
    (rpt strip_tac >> drule_all opt_mmap_el >> simp[]) >>
  `MAP (type_memory_bytes cenv) tys = MAP type_memory_size tvs` by
    (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
     qpat_assum `!ty rt. _ ==> type_memory_bytes cenv ty = _` irule >> simp[]) >>
  `!tr. MAP (elem_size_in_location cenv (slot_loc tr)) tys = MAP type_slot_size tvs` by
    (gen_tac >> irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
     `type_memory_bytes cenv (EL x tys) = type_memory_size (EL x tvs)` by
       (qpat_assum `!ty rt. _ ==> type_memory_bytes cenv ty = _` irule >> simp[]) >>
     Cases_on `tr` >> simp[elem_size_in_location_def, is_slot_addressed_def,
                           slot_loc_def, slot_count_of_memory_size]) >>
  `k < LENGTH tvs` by simp[] >>
  `type_memory_bytes cenv (EL k tys) = type_memory_size (EL k tvs)` by
    (qpat_assum `!ty rt. _ ==> type_memory_bytes cenv ty = _` irule >> simp[]) >>
  `elem_size_in_location cenv LocMemory = type_memory_bytes cenv /\
   elem_size_in_location cenv LocCode = type_memory_bytes cenv` by
    simp[FUN_EQ_THM, elem_size_in_location_def, is_slot_addressed_def] >>
  simp[tuple_offset_def, tuple_prefix_slot_size_sum, MAP_TAKE,
       mem_step_offset_def, type_memory_size_list_sum] >>
  conj_tac
  >- (drule_then mp_tac tuple_element_interval >>
      simp[MAP_TAKE, valueEncodingTheory.type_memory_size_def, type_memory_size_list_sum]) >>
  qspecl_then [`MAP type_slot_size tvs`,`k`] mp_tac sum_take_el_le >>
  simp[EL_MAP, MAP_TAKE, vyperValueTheory.type_slot_size_def,
       vyperStorageRegionWriteTheory.type_slot_size_list_sum]
QED
