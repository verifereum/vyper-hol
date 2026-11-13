(* Structural types whose paths never select a dynamic-array header. *)
Theory dynarrayFreeProps
Ancestors
  exprSimProps loweringPosts supportedTypes vyperTyping vyperTypeSystem vyperValue
  valueEncoding valueEncodingDefs list option pair

Theorem dynarray_free_tuple:
  !tvs. EVERY dynarray_free tvs ==> dynarray_free (TupleTV tvs)
Proof
  rw[dynarray_free_def] >> Cases_on `path` >>
  simp[mem_path_offset_def, AllCaseEqs(), optionTheory.OPTION_MAP_EQ_SOME,
       EXISTS_PROD, PULL_EXISTS] >>
  rpt strip_tac >> drule mem_step_offset_shape >> strip_tac >> gvs[] >>
  fs[EVERY_EL,dynarray_free_def] >> metis_tac[]
QED

Theorem supported_scalar_evaluate_dynarray_free:
  supported_scalar_type ty /\ evaluate_type tenv ty = SOME tv ==>
  dynarray_free tv
Proof
  Cases_on `ty` >>
  simp[supported_scalar_type_def,supported_word_type_def,supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def,supported_string_type_def,evaluate_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >>
       simp[supported_word_type_def,supported_string_type_def,evaluate_type_def]) >>
  rpt strip_tac >> gvs[] >> simp[dynarray_free_base]
QED
