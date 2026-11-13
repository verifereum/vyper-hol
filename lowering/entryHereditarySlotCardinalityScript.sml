Theory entryHereditarySlotCardinality
Ancestors
  entrySourceSlotBounds entryAssignableCardinality entrySourceEncodingAlignment
  vyperABI vyperTypeABI vyperTypeSystem vyperValue vyperTypeDefaults contractABI words
  vyperStorageRegionWrite entryDecodeProps valueEncodingProofs list rich_list

Definition entry_tuple_cardinality_def:
  entry_tuple_cardinality (Tuple tys) =
    (LENGTH tys < dimword (:256) /\ EVERY entry_tuple_cardinality tys) /\
  entry_tuple_cardinality (Array bd ty) = entry_tuple_cardinality ty /\
  entry_tuple_cardinality _ = T
End

Theorem entry_tuple_cardinality_tuple[simp]:
  entry_tuple_cardinality (Tuple tys) <=>
  LENGTH tys < dimword (:256) /\ EVERY entry_tuple_cardinality tys
Proof
  simp[entry_tuple_cardinality_def, ETA_THM]
QED

Theorem entry_tuple_cardinality_array[simp]:
  entry_tuple_cardinality (Array bd ty) <=> entry_tuple_cardinality ty
Proof
  simp[entry_tuple_cardinality_def, ETA_THM]
QED

Theorem source_slot_tuple_cardinality:
  !env ty. assignable_type env ty ==> !tv.
    evaluate_type env ty = SOME tv /\ type_slot_size tv < dimword (:256) ==>
    entry_tuple_cardinality (vyper_to_abi_type env ty)
Proof
  ho_match_mp_tac assignable_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`NoneT`] >- simp[assignable_type_def]
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> simp[vyper_to_abi_type_def, vyper_base_to_abi_type_def,
                          entry_tuple_cardinality_def] >>
      Cases_on `b` >> simp[entry_tuple_cardinality_def])
  >~ [`FlagT nsid`] >- simp[vyper_to_abi_type_def, entry_tuple_cardinality_def]
  >~ [`ArrayT ty bd`] >- suspend "array"
  >~ [`TupleT tys`] >- suspend "tuple"
  >> suspend "struct"
QED

Resume source_slot_tuple_cardinality[array]:
  rpt strip_tac >>
  gvs[Once assignable_type_def, Once evaluate_type_def, AllCaseEqs()] >>
  Cases_on `bd` >> simp[vyper_to_abi_type_def] >>
  first_x_assum irule >> simp[] >>
  gvs[vyperASTTheory.bound_length_def, type_slot_size_def] >>
  Cases_on `n` >> gvs[arithmeticTheory.MULT_CLAUSES] >> decide_tac
QED

Resume source_slot_tuple_cardinality[tuple]:
  rpt strip_tac >> drule_all assignable_tuple_evaluation >> strip_tac >>
  drule_all evaluated_assignable_members_slot_bound >> strip_tac >>
  simp[Once vyper_to_abi_type_def] >>
  conj_tac >- gvs[type_slot_size_def, vyper_to_abi_types_length] >>
  gvs[EVERY_EL, LIST_REL_EL_EQN, vyper_to_abi_types_length,
      vyper_to_abi_types_EL] >> rpt strip_tac >>
  first_x_assum irule >>
  `MEM (EL n tys) tys` by (irule EL_MEM >> simp[]) >>
  simp[] >>
  `evaluate_type env (EL n tys) = SOME (EL n tvs)` by simp[] >>
  drule_all evaluated_tuple_child_slot_bound >> simp[]
QED

Resume source_slot_tuple_cardinality[struct]:
  rpt strip_tac >> drule_all assignable_struct_evaluation >> strip_tac >>
  `EVERY (assignable_type (env \\ nsid)) (MAP SND fields)` by
    (gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  drule_all evaluated_assignable_members_slot_bound >> strip_tac >>
  simp[Once vyper_to_abi_type_def] >>
  conj_tac >- (gvs[type_slot_size_def, vyper_to_abi_types_length] >>
              gvs[type_slot_size_fields_list, MAP_ZIP]) >>
  gvs[EVERY_EL, LIST_REL_EL_EQN, vyper_to_abi_types_length,
      vyper_to_abi_types_EL, EL_MAP] >> rpt strip_tac >>
  first_x_assum irule >>
  `MEM (EL n fields) fields` by (irule EL_MEM >> simp[]) >>
  simp[] >>
  `evaluate_type (env \\ nsid) (SND (EL n fields)) = SOME (EL n tvs)` by simp[] >>
  `MEM (FST (EL n fields), SND (EL n fields)) fields` by simp[] >>
  drule_all evaluated_struct_child_slot_bound >> simp[]
QED

Finalise source_slot_tuple_cardinality

Theorem evaluated_array_element_tuple_cardinality:
  assignable_type env (ArrayT ty bd) /\
  evaluate_type env (ArrayT ty bd) = SOME tv ==>
  entry_tuple_cardinality (vyper_to_abi_type env ty)
Proof
  strip_tac >>
  gvs[Once assignable_type_def, Once evaluate_type_def, AllCaseEqs()] >>
  irule source_slot_tuple_cardinality >> simp[] >>
  `evaluate_type env (ArrayT ty bd) = SOME (ArrayTV tv' bd)` by
    simp[Once evaluate_type_def] >>
  drule_all evaluated_array_child_slot_bound >> simp[]
QED
