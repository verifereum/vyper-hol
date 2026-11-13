(* Current-value tuple layout; no historical place or execution assertion. *)
Theory bodyPtrSubscriptTupleLayout
Ancestors
  bodyPtrSubscriptCurrentMemory tupleMemoryLayout exprSimProps
  exprSimDefs exprSimHyps compileEnv exprLowering loweringPosts valueEncoding valueEncodingProofs vyperTypeABI
  vyperTypeDefaults vyperValue vyperTyping vyperTypeSystem vyperState vyperValueOperation
  list rich_list

Theorem tuple_memory_sizes:
  !tys tvs cenv cx env es.
    expr_sim_inv cenv cx env es /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs ==>
    MAP (elem_size_in_location cenv LocMemory) tys = MAP type_memory_size tvs
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `evaluate_type (get_tenv cx) h` >> gvs[] >>
  Cases_on `OPT_MMAP (evaluate_type (get_tenv cx)) tys` >> gvs[] >>
  rename1 `evaluate_type _ h = SOME htv` >>
  `type_memory_bytes cenv h = type_memory_size htv` by
    (irule expr_sim_inv_memory_size >> metis_tac[]) >>
  first_x_assum drule_all >> simp[elem_size_in_location_def, is_slot_addressed_def]
QED

Theorem typed_tuple_child_layout:
  expr_sim_inv cenv cx env es /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME tv /\
  value_has_type tv v /\ k < LENGTH tys ==>
  ?child off ctv.
    evaluate_subscripts tv v [ValueSubscript (IntV (&k))] = INL child /\
    mem_step_offset tv (ValueSubscript (IntV (&k))) = SOME (off,ctv) /\
    off = SUM (TAKE k (MAP (elem_size_in_location cenv LocMemory) tys)) /\
    off + type_memory_size ctv <= type_memory_size tv /\
    evaluate_type (get_tenv cx) (EL k tys) = SOME ctv /\
    value_has_type ctv child
Proof
  strip_tac >> gvs[Once evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `value_has_type (TupleTV _) (ArrayV av)` >>
  Cases_on `av` >> gvs[value_has_type_def] >>
  drule_all tuple_memory_sizes >> strip_tac >>
  drule OPT_MMAP_LIST_REL >> strip_tac >>
  drule OPT_MMAP_LENGTH >> strip_tac >>
  drule values_have_types_length >> strip_tac >>
  gvs[] >> qexistsl_tac [`EL k l`, `EL k tvs`] >>
  simp[evaluate_subscripts_def, array_index_def, mem_step_offset_def,
       type_memory_size_def, type_memory_size_list_sum, MAP_TAKE, oEL_THM] >>
  conj_tac >- (qspec_then `tvs` mp_tac tuple_element_interval >>
    simp[GSYM MAP_TAKE]) >>
  conj_tac >- fs[LIST_REL_EL_EQN] >>
  fs[values_have_types_LIST_REL, LIST_REL_EL_EQN]
QED
