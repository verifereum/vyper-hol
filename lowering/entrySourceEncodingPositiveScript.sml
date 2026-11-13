Theory entrySourceEncodingPositive
Ancestors
  entrySourceDefaultPositive entrySourceEncodingAlignment entryConversionPositive
  entryDefaultEncodingPositive entryEncodingPositive vyperABI vyperValue vyperTypeSystem vyperTyping
  valueEncodingProofs vyperAssignPreservesType vyperABIRoundtrip entryDecodeProps contractABI byte list rich_list

Theorem source_encoding_positive:
  !env ty. assignable_type env ty ==>
  !tv v av. evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av ==>
    0 < LENGTH (enc (vyper_to_abi_type env ty) av)
Proof
  ho_match_mp_tac assignable_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`NoneT`]
  >- simp[assignable_type_def]
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> rpt strip_tac >> Cases_on `v` >>
      gvs[vyper_to_abi_def, vyper_to_abi_base_def, vyper_base_to_abi_type_def, enc_def,
          enc_number_def, LENGTH_word_to_bytes] >>
      Cases_on `b` >> gvs[enc_def, enc_number_def, LENGTH_word_to_bytes] >>
      gvs[evaluate_type_def, value_has_type_def, AllCaseEqs()] >>
      simp[TAKE_LENGTH_TOO_LONG])
  >~ [`FlagT nsid`]
  >- (rpt strip_tac >> Cases_on `v` >>
      gvs[vyper_to_abi_def, enc_def, enc_number_def, LENGTH_word_to_bytes])
  >~ [`TupleT tys`]
  >- (rpt strip_tac >> drule_all assignable_tuple_evaluation >> strip_tac >>
      Cases_on `v` >> gvs[value_has_type_def, Excl "enc_def"] >>
      rename1 `value_has_type (TupleTV _) (ArrayV arr)` >> Cases_on `arr` >>
      gvs[value_has_type_def, Excl "enc_def"] >>
      gvs[Once vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
      irule tuple_encoding_positive_member >>
      drule vyper_to_abi_list_EL >> strip_tac >>
      conj_tac >- simp[vyper_to_abi_types_length] >>
      drule_all evaluated_assignable_values_alignment >> strip_tac >>
      `EVERY (\p. 0 < LENGTH (enc (FST p) (SND p)))
        (ZIP (vyper_to_abi_types env tys,avs))` by
        (irule list_conversion_encoding_positive >>
         qexists `\ty v. MEM ty tys /\ assignable_type env ty /\
           ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v` >>
         qexists `l` >> simp[] >> conj_tac >- metis_tac[] >>
         gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
         metis_tac[MEM_EL]) >>
      Cases_on `tys` >> Cases_on `avs` >>
      gvs[Once vyper_to_abi_type_def, Excl "enc_def"])
  >~ [`ArrayT ty bd`] >- suspend "array"
  >> suspend "struct"
QED

Resume source_encoding_positive[array]:
  rpt strip_tac >>
  gvs[Once assignable_type_def, Once evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def, Excl "enc_def"] >>
  rename1 `value_has_type (ArrayTV _ _) (ArrayV arr)` >> Cases_on `arr` >>
  gvs[value_has_type_def, Excl "enc_def"] >>
  Cases_on `bd` >>
  gvs[value_has_type_def, Once vyper_to_abi_type_def,
      vyperASTTheory.bound_length_def, AllCaseEqs(), Excl "enc_def"]
  >~ [`Array NONE _`] >- irule dynamic_array_encoding_positive
  >> irule sparse_fixed_encoding_positive >>
  conj_tac >- simp[] >>
  qexistsl [`env`, `l`, `tv'`, `ty`] >> simp[] >>
  reverse conj_tac >- metis_tac[source_default_encoding_positive] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[ALOOKUP_sparse_has_type]
QED

Resume source_encoding_positive[struct]:
  rpt strip_tac >> drule_all assignable_struct_evaluation >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, Excl "enc_def"] >>
  gvs[Once vyper_to_abi_def, AllCaseEqs(), Excl "enc_def"] >>
  drule struct_has_type_values_have_types >>
  `LENGTH fields = LENGTH tvs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  simp[MAP_ZIP, Excl "enc_def"] >> strip_tac >>
  irule tuple_encoding_positive_member >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  conj_tac >- simp[vyper_to_abi_types_length] >>
  `EVERY (assignable_type (env \\ nsid)) (MAP SND fields)` by
    (gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  drule_all evaluated_assignable_values_alignment >> strip_tac >>
  `EVERY (\p. 0 < LENGTH (enc (FST p) (SND p)))
    (ZIP (vyper_to_abi_types (env \\ nsid) (MAP SND fields),avs))` by
    (irule list_conversion_encoding_positive >>
     qexists `\ty v. MEM ty (MAP SND fields) /\
       assignable_type (env \\ nsid) ty /\
       ?tv. evaluate_type (env \\ nsid) ty = SOME tv /\ value_has_type tv v` >>
     qexists `MAP SND l` >> simp[] >>
     conj_tac >- (rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[]) >>
     gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule EL_MEM >> simp[]) >>
  Cases_on `fields` >> Cases_on `avs` >>
  gvs[Once vyper_to_abi_type_def, Excl "enc_def"]
QED

Finalise source_encoding_positive
