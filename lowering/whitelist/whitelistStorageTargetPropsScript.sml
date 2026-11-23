Theory whitelistStorageTargetProps
Ancestors
  supportedDecls supportedExprForms supportedStmts supportedTargets supportedTypes option pair

Theorem storage_value_scalar_target:
  supported_storage_value tops k ty ==> supported_scalar_target tops k
Proof
  rw[supported_storage_value_def, supported_scalar_target_def] >>
  Cases_on `supported_variable_decl tops k` >> gvs[] >>
  rename1 `SOME vd` >> PairCases_on `vd` >> gvs[] >>
  Cases_on `vd1` >> Cases_on `vd3` >> gvs[]
QED

Theorem storage_value_dynamic_array:
  supported_storage_value tops k (ArrayT elem (Dynamic n)) ==>
  supported_storage_dynamic_array tops k
Proof
  rw[supported_storage_value_def, supported_storage_dynamic_array_def] >>
  Cases_on `supported_variable_decl tops k` >> gvs[] >>
  rename1 `SOME vd` >> PairCases_on `vd` >> gvs[] >>
  Cases_on `vd1` >> Cases_on `vd3` >> gvs[supported_storage_type_def] >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def]
QED

Theorem supported_place_root_target_info:
  supported_place_root tops id ==>
  IS_SOME (supported_target_info tops bindings (TopLevelNameTarget id))
Proof
  Cases_on `FST id = NONE` >> simp[supported_place_root_def, supported_target_info_def] >>
  Cases_on `supported_variable_decl tops id` >> simp[]
  >- (Cases_on `supported_hashmap_decl tops id` >> simp[] >>
      rename1 `supported_hashmap_decl tops id = SOME hm` >> PairCases_on `hm` >> simp[]) >>
  rename1 `supported_variable_decl tops id = SOME vd` >> PairCases_on `vd` >> simp[] >>
  Cases_on `supported_hashmap_decl tops id` >> simp[] >>
  rename1 `supported_hashmap_decl tops id = SOME hm` >> PairCases_on `hm` >> simp[]
QED
