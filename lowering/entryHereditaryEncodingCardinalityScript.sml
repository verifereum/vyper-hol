Theory entryHereditaryEncodingCardinality
Ancestors
  entryHereditarySlotCardinality entrySourceEncodingPositive
  entrySourceEncodingAlignment entryConversionPositive entryEncodingCardinality
  vyperABI vyperABIRoundtrip vyperTypeABI vyperValue vyperTyping vyperTypeSystem
  valueEncodingProofs entryDecodeProps contractABI list rich_list words

Theorem source_list_encoding_positive[local]:
  LIST_REL (\ty v. assignable_type env ty /\
    ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vs /\
  vyper_to_abi_list env tys vs = SOME avs ==>
  EVERY (\p. 0 < LENGTH (enc (FST p) (SND p)))
    (ZIP (vyper_to_abi_types env tys,avs))
Proof
  strip_tac >> irule list_conversion_encoding_positive >>
  qexists `\ty v. assignable_type env ty /\
    ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v` >>
  qexists `vs` >> simp[] >> metis_tac[source_encoding_positive]
QED

Theorem source_encoding_tuple_cardinality:
  !env ty. assignable_type env ty ==> !tv v av.
    evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\
    LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) ==>
    entry_tuple_cardinality (vyper_to_abi_type env ty)
Proof
  ho_match_mp_tac assignable_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`NoneT`] >- simp[assignable_type_def]
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> simp[vyper_to_abi_type_def, vyper_base_to_abi_type_def,
                          entry_tuple_cardinality_def] >>
      Cases_on `b` >> simp[entry_tuple_cardinality_def])
  >~ [`FlagT nsid`] >- simp[vyper_to_abi_type_def, entry_tuple_cardinality_def]
  >~ [`ArrayT ty bd`]
  >- (rpt strip_tac >> drule_all evaluated_array_element_tuple_cardinality >>
      Cases_on `bd` >> simp[vyper_to_abi_type_def])
  >~ [`TupleT tys`] >- suspend "tuple"
  >> suspend "struct"
QED

Resume source_encoding_tuple_cardinality[tuple]:
  rpt strip_tac >> drule_all assignable_tuple_evaluation >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, Excl "enc_def"] >>
  rename1 `value_has_type (TupleTV _) (ArrayV arr)` >> Cases_on `arr` >>
  gvs[value_has_type_def, Excl "enc_def"] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  drule_all evaluated_assignable_values_alignment >> strip_tac >>
  conj_tac
  >- (irule tuple_encoding_positive_member_count >>
      qexists `avs` >> simp[vyper_to_abi_types_length] >>
      irule source_list_encoding_positive >> metis_tac[]) >>
  gvs[EVERY_EL, LIST_REL_EL_EQN, vyper_to_abi_types_length,
      vyper_to_abi_types_EL] >> rpt strip_tac >>
  `MEM (EL n tys) tys` by (irule EL_MEM >> simp[]) >>
  `LENGTH (enc (vyper_to_abi_type env (EL n tys)) (EL n avs)) <
    dimword (:256)` by
    (`LENGTH (enc (EL n (vyper_to_abi_types env tys)) (EL n avs)) <=
       LENGTH (enc (Tuple (vyper_to_abi_types env tys)) (ListV avs))` by
       (irule tuple_encoding_member_bound >> simp[vyper_to_abi_types_length]) >>
     gvs[vyper_to_abi_types_EL]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume source_encoding_tuple_cardinality[struct]:
  rpt strip_tac >> drule_all assignable_struct_evaluation >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, Excl "enc_def"] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
  drule struct_has_type_values_have_types >>
  `LENGTH fields = LENGTH tvs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  simp[MAP_ZIP, Excl "enc_def"] >> strip_tac >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  `EVERY (assignable_type (env \\ nsid)) (MAP SND fields)` by
    (gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  drule_all evaluated_assignable_values_alignment >> strip_tac >>
  conj_tac
  >- (irule tuple_encoding_positive_member_count >>
      qexists `avs` >> simp[vyper_to_abi_types_length] >>
      irule source_list_encoding_positive >> metis_tac[]) >>
  gvs[EVERY_EL, LIST_REL_EL_EQN, vyper_to_abi_types_length,
      vyper_to_abi_types_EL, EL_MAP] >> rpt strip_tac >>
  `MEM (EL n fields) fields` by (irule EL_MEM >> simp[]) >>
  `LENGTH (enc (vyper_to_abi_type (env \\ nsid) (SND (EL n fields)))
    (EL n avs)) < dimword (:256)` by
    (`LENGTH (enc (EL n (vyper_to_abi_types (env \\ nsid) (MAP SND fields)))
       (EL n avs)) <= LENGTH (enc
       (Tuple (vyper_to_abi_types (env \\ nsid) (MAP SND fields))) (ListV avs))` by
       (irule tuple_encoding_member_bound >> simp[vyper_to_abi_types_length]) >>
     gvs[vyper_to_abi_types_EL, EL_MAP]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Finalise source_encoding_tuple_cardinality
