Theory entryAbiStructTyping
Ancestors
  entryAbiTupleTyping entrySourceEncodingAlignment entryHereditarySlotCardinality
  entryDecodeProps vyperABI vyperABIRoundtrip vyperTypeABI vyperTypeSystem
  vyperTyping vyperValue contractABI valueEncodingProofs list rich_list words
  finite_map pair

Theorem entry_struct_abi_conversion_typed:
  FLOOKUP env nsid = SOME (StructArgs fields) /\
  (!ty. MEM ty (MAP SND fields) ==> !tv v av.
     evaluate_type (env \\ nsid) ty = SOME tv /\ value_has_type tv v /\
     abi_decode_bytes_widths (env \\ nsid) ty /\
     entry_tuple_cardinality (vyper_to_abi_type (env \\ nsid) ty) /\
     vyper_to_abi (env \\ nsid) ty v = SOME av ==>
     has_type (vyper_to_abi_type (env \\ nsid) ty) av) /\
  assignable_type env (StructT nsid) /\
  evaluate_type env (StructT nsid) = SOME tv /\ value_has_type tv v /\
  abi_decode_bytes_widths env (StructT nsid) /\
  entry_tuple_cardinality (vyper_to_abi_type env (StructT nsid)) /\
  vyper_to_abi env (StructT nsid) v = SOME av ==>
  has_type (vyper_to_abi_type env (StructT nsid)) av
Proof
  strip_tac >> drule_all assignable_struct_evaluation >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
  drule struct_has_type_values_have_types >>
  `LENGTH fields = LENGTH tvs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  simp[MAP_ZIP] >> strip_tac >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  `EVERY (assignable_type (env \\ nsid)) (MAP SND fields)` by
    (gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  drule_all evaluated_assignable_values_alignment >> strip_tac >>
  gvs[vyper_to_abi_type_def, entry_tuple_cardinality_tuple,
      abi_decode_bytes_widths_def, has_type_def, has_types_LIST_REL,
      LIST_REL_EL_EQN, EVERY_EL, vyper_to_abi_types_length,
      vyper_to_abi_types_EL] >> rpt strip_tac >>
  `MEM (EL n (MAP SND fields)) (MAP SND fields)` by
    (irule EL_MEM >> simp[]) >>
  first_x_assum irule >> gvs[EL_MAP] >> metis_tac[]
QED
