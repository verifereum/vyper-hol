Theory extRetSupportedShapePtr
Ancestors extRetRecursivePlanPtr supportedPlaceAssignable supportedTypes
  vyperTypeSystem vyperValue finite_map list option

Theorem supported_nested_encodable_ret_shape:
  !leaf fuel tops ty. !tenv.
    supported_nested_type leaf fuel tops ty /\ leaf = supported_scalar_type /\
    tenv SUBMAP type_env tops /\ well_formed_type tenv ty ==>
    encodable_ret_shape tenv ty
Proof
  recInduct supported_nested_type_ind >> rpt strip_tac >>
  gvs[] >>
  qpat_x_assum `supported_nested_type _ _ _ ty` mp_tac >>
  Cases_on `ty` >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def] >> strip_tac >> gvs[]
  >~ [`encodable_ret_shape tenv (BaseT bt)`]
  >- (irule (cj 1 encodable_ret_shape_rules) >>
      gvs[well_formed_type_def, IS_SOME_EXISTS] >> metis_tac[])
  >~ [`encodable_ret_shape tenv (BaseT bt)`]
  >- (irule (cj 1 encodable_ret_shape_rules) >>
      gvs[well_formed_type_def, IS_SOME_EXISTS] >> metis_tac[])
  >~ [`encodable_ret_shape tenv (TupleT ts)`]
  >- (drule well_formed_tuple_elements >> strip_tac >>
      irule (cj 4 encodable_ret_shape_rules) >>
      conj_tac
      >- (gvs[well_formed_type_def, IS_SOME_EXISTS] >> metis_tac[]) >>
      gvs[EVERY_MEM] >> metis_tac[])
  >~ [`encodable_ret_shape tenv (ArrayT t bd)`]
  >- (drule well_formed_array_element >> strip_tac >>
      irule (cj 3 encodable_ret_shape_rules) >> conj_tac
      >- (gvs[well_formed_type_def, IS_SOME_EXISTS] >> metis_tac[]) >>
      Cases_on `bd` >> gvs[] >> metis_tac[])
  >> Cases_on `supported_struct_fields tops p` >> gvs[] >>
  rename1 `supported_struct_fields tops p = SOME fields` >>
  drule_all supported_struct_submap_lookup >> strip_tac >>
  drule_all well_formed_struct_fields_deleted >> strip_tac >>
  `tenv \\ p SUBMAP type_env tops` by
    (fs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
     rpt strip_tac >> first_x_assum irule >> gvs[]) >>
  irule (cj 5 encodable_ret_shape_rules) >>
  conj_tac
  >- (gvs[well_formed_type_def, IS_SOME_EXISTS] >> metis_tac[]) >>
  qexists `fields` >> simp[] >>
  gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
  gvs[] >> metis_tac[]
QED

Theorem supported_place_encodable_ret_shape:
  supported_place_type tops ty /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  encodable_ret_shape (type_env tops) ty
Proof
  strip_tac >> irule supported_nested_encodable_ret_shape >>
  simp[supported_place_type_def, well_formed_type_def] >>
  qexistsl [`LENGTH tops`, `tops`] >>
  gvs[supported_place_type_def]
QED

Theorem supported_place_abi_enc_plan:
  supported_place_type tops ty /\
  evaluate_type (type_env tops) ty = SOME tv /\
  sfields_tenv_consistent sf (type_env tops) /\
  (!k a. FLOOKUP (type_env tops) k = SOME (StructArgs a) ==> FST k = NONE) /\
  sfields_tenv_consistent cenv.ce_struct_fields (type_env tops) /\
  (!t tv. evaluate_type (type_env tops) t = SOME tv ==>
     type_memory_bytes cenv t = type_memory_size tv) ==>
  abi_enc_plan (type_env tops) ty (type_to_abi_enc_info sf cenv ty)
Proof
  strip_tac >> irule encodable_ret_shape_plan >>
  simp[] >> drule_all supported_place_encodable_ret_shape >> strip_tac >> simp[] >>
  qexists `type_env tops` >> simp[]
QED
