Theory entryAbiTupleTyping
Ancestors
  entryHereditarySlotCardinality entrySourceEncodingAlignment entryDecodeProps
  vyperABI vyperABIRoundtrip vyperTypeABI vyperTypeSystem vyperTyping vyperValue
  contractABI valueEncodingProofs list rich_list words

Theorem entry_tuple_abi_conversion_typed:
  (!ty. MEM ty tys ==> !tv v av.
     evaluate_type env ty = SOME tv /\ value_has_type tv v /\
     abi_decode_bytes_widths env ty /\
     entry_tuple_cardinality (vyper_to_abi_type env ty) /\
     vyper_to_abi env ty v = SOME av ==>
     has_type (vyper_to_abi_type env ty) av) /\
  assignable_type env (TupleT tys) /\
  evaluate_type env (TupleT tys) = SOME tv /\ value_has_type tv v /\
  abi_decode_bytes_widths env (TupleT tys) /\
  entry_tuple_cardinality (vyper_to_abi_type env (TupleT tys)) /\
  vyper_to_abi env (TupleT tys) v = SOME av ==>
  has_type (vyper_to_abi_type env (TupleT tys)) av
Proof
  strip_tac >> drule_all assignable_tuple_evaluation >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  Cases_on `a` >> gvs[value_has_type_def] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs()] >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  drule_all evaluated_assignable_values_alignment >> strip_tac >>
  gvs[vyper_to_abi_type_def, entry_tuple_cardinality_tuple,
      abi_decode_bytes_widths_def, has_type_def, has_types_LIST_REL,
      LIST_REL_EL_EQN, EVERY_EL, vyper_to_abi_types_length,
      vyper_to_abi_types_EL] >> rpt strip_tac >>
  `MEM (EL n tys) tys` by (irule EL_MEM >> simp[]) >>
  first_x_assum irule >> metis_tac[]
QED
