Theory whitelistEventTypeProps
Ancestors
  supportedTypes vyperAST vyperTypeContract vyperTypeSystem whitelistCheckerTypes

Theorem checker_indexed_event_type_supported:
  assignable_type tenv ty /\ event_indexable_type ty ==>
  supported_event_leaf_type ty
Proof
  Cases_on `ty` >> simp[event_indexable_type_def, supported_event_leaf_type_def]
  >- (strip_tac >> fs[assignable_type_def] >>
      drule well_formed_base_scalar >> strip_tac >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[supported_scalar_type_def, supported_word_type_def]) >>
  simp[supported_scalar_type_def]
QED
