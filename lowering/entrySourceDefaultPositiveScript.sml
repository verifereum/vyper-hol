Theory entrySourceDefaultPositive
Ancestors
  entrySourceEncodingAlignment entryDefaultEncodingPositive vyperTypeSystem
  vyperABI vyperValue vyperTypeABI valueEncodingProofs entryDecodeProps list rich_list

Theorem source_default_encoding_positive:
  !env ty. assignable_type env ty ==>
  !tv. evaluate_type env ty = SOME tv ==>
    0 < LENGTH (enc (vyper_to_abi_type env ty) (default_to_abi tv))
Proof
  ho_match_mp_tac assignable_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`BaseT bt`]
  >- (metis_tac[default_base_encoding_positive])
  >~ [`FlagT nsid`]
  >- (metis_tac[default_flag_encoding_positive])
  >~ [`NoneT`]
  >- simp[assignable_type_def]
  >~ [`TupleT tys`]
  >- (rpt strip_tac >> drule_all assignable_tuple_evaluation >> strip_tac >>
      gvs[Once vyper_to_abi_type_def] >>
      irule default_tuple_encoding_positive >>
      conj_tac >- (Cases_on `tys` >> gvs[]) >>
      gvs[LIST_REL_EL_EQN, EVERY_MEM, vyper_to_abi_types_length,
          vyper_to_abi_types_EL] >> rpt strip_tac >>
      first_x_assum irule >> metis_tac[MEM_EL, vyper_to_abi_types_length,
                                    vyper_to_abi_types_EL])
  >~ [`ArrayT ty bd`]
  >- (rpt strip_tac >>
      gvs[Once assignable_type_def, Once evaluate_type_def, AllCaseEqs()] >>
      Cases_on `bd` >> gvs[Once vyper_to_abi_type_def] >>
      metis_tac[default_fixed_array_encoding_positive,
                default_dynamic_array_encoding_positive, vyperASTTheory.bound_length_def]) >>
  rpt strip_tac >> drule_all assignable_struct_evaluation >> strip_tac >>
  gvs[Once vyper_to_abi_type_def] >>
  irule default_struct_encoding_positive >>
  `LENGTH fields = LENGTH tvs` by
    metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  simp[MAP_ZIP, vyper_to_abi_types_length] >>
  conj_tac >- (Cases_on `fields` >> gvs[]) >>
  gvs[LIST_REL_EL_EQN, EVERY_MEM, vyper_to_abi_types_length,
      vyper_to_abi_types_EL, EL_MAP] >> rpt strip_tac >>
  first_x_assum irule >> simp[MEM_EL] >>
  metis_tac[MEM_EL, EL_MAP]
QED
