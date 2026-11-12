Theory entrySourceSlotBounds
Ancestors
  arithmetic combin list rich_list finite_map words vyperValue vyperAST
  vyperTypeDefaults vyperStorageRegionWrite

Theorem evaluated_member_slot_bound[local]:
  !tys tvs tenv ty child.
    evaluate_types tenv tys [] = SOME tvs /\ MEM ty tys /\
    evaluate_type tenv ty = SOME child ==>
    type_slot_size child <= type_slot_size_list tvs
Proof
  Induct >> simp[evaluate_types_OPT_MMAP, OPT_MMAP_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs(), type_slot_size_def] >>
  first_x_assum (qspecl_then [`t`, `tenv`, `ty`, `child`] mp_tac) >>
  simp[evaluate_types_OPT_MMAP] >> decide_tac
QED

Theorem evaluated_tuple_child_slot_bound:
  evaluate_type tenv (TupleT tys) = SOME tv /\ MEM ty tys /\
  evaluate_type tenv ty = SOME child ==>
  type_slot_size child <= type_slot_size tv
Proof
  simp[Once evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  gvs[type_slot_size_def] >>
  drule_all evaluated_member_slot_bound >> simp[]
QED

Theorem evaluated_struct_child_slot_bound:
  FLOOKUP tenv nsid = SOME (StructArgs fields) /\
  evaluate_type tenv (StructT nsid) = SOME tv /\ MEM (name,ty) fields /\
  evaluate_type (tenv \\ nsid) ty = SOME child ==>
  type_slot_size child <= type_slot_size tv
Proof
  strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs(), type_slot_size_def] >>
  `MEM ty (MAP SND fields)` by (simp[MEM_MAP] >> qexists_tac `(name,ty)` >> simp[]) >>
  drule evaluate_types_length >> simp[] >> strip_tac >>
  drule_all evaluated_member_slot_bound >>
  simp[type_slot_size_fields_list, MAP_ZIP]
QED

Theorem evaluated_array_child_slot_bound:
  evaluate_type tenv (ArrayT ty bd) = SOME tv /\
  evaluate_type tenv ty = SOME child ==>
  type_slot_size child <= type_slot_size tv /\
  type_slot_size child < dimword (:256)
Proof
  simp[Once evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `bd` >> gvs[type_slot_size_def, bound_length_def] >>
  rename1 `0 < n` >> Cases_on `n` >> gvs[MULT_CLAUSES] >> decide_tac
QED
