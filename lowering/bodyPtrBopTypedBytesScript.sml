Theory bodyPtrBopTypedBytes
Ancestors
  bodyPtrBopClassification compileEnv exprSimHypsDefs vyperTypeSystem
  vyperValue vyperTyping

Theorem bop_machine_word_not_bytestring:
  is_word_type ty ==> ~is_bytestring_type ty
Proof
  Cases_on `ty` >> simp[is_word_type_def, is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_word_type_def, is_bytestring_type_def]
QED


Theorem bop_byte_typed_values:
  is_word_type ty /\ is_word_type ty2 /\
  ~(word_value_type ty /\ word_value_type ty2) /\
  bop <> In /\ bop <> NotIn /\ well_typed_binop ann bop ty ty2 /\
  evaluate_type tenv ty = SOME tv1 /\ evaluate_type tenv ty2 = SOME tv2 /\
  value_has_type tv1 v1 /\ value_has_type tv2 v2 ==>
  (bop = Eq \/ bop = NotEq) /\ ty2 = ty /\ tv2 = tv1 /\
  (tv1 = BaseTV AddressT \/ ?m. tv1 = BaseTV (BytesT (Fixed m)) /\ m <= 32) /\
  ?b1 b2. v1 = BytesV b1 /\ v2 = BytesV b2
Proof
  strip_tac >>
  `~((bop = Eq \/ bop = NotEq) /\ is_bytestring_type ty)` by
    metis_tac[bop_machine_word_not_bytestring] >>
  drule_all bop_nonresidual_type_partition >> strip_tac >> gvs[] >>
  gvs[is_word_type_def, well_typed_binop_def, evaluate_type_def] >>
  Cases_on `v1` >> Cases_on `v2` >> gvs[value_has_type_def]
QED

Theorem bop_nonresidual_machine_types:
  well_typed_binop ann bop ty1 ty2 /\ bop <> In /\ bop <> NotIn /\
  ~((bop = Eq \/ bop = NotEq) /\ is_bytestring_type ty1) /\
  IS_SOME (evaluate_type tenv ty1) ==>
  is_word_type ty1 /\ is_word_type ty2
Proof
  strip_tac >> drule_all bop_nonresidual_type_partition >> strip_tac
  >- metis_tac[exprSimSourceTheory.word_value_type_word] >>
  gvs[well_typed_binop_def, evaluate_type_def, is_word_type_def] >>
  gvs[AllCaseEqs()]
QED
