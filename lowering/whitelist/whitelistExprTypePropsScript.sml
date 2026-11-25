Theory whitelistExprTypeProps
Ancestors
  vyperAST vyperTypeSystem vyperTypeContract option list
  supportedTypes supportedExprForms whitelistCheckerTypes

Theorem valid_conversion_nonaggregate:
  valid_conversion s t ==>
  (case t of ArrayT _ _ => F | TupleT _ => F | _ => T)
Proof
  Cases_on `t` >> simp[] >>
  Cases_on `s` >> simp[valid_conversion_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[valid_conversion_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[valid_conversion_def]
QED

Theorem check_value_type_subscript_child:
  check_value_type tenv vt /\ subscript_vtype vt kty = SOME vt' ==>
  check_value_type tenv vt'
Proof
  Cases_on `vt` >> simp[check_value_type_def] >> rpt strip_tac
  >- (rename1 `subscript_vtype (Type ty)` >> Cases_on `ty` >>
      gvs[subscript_vtype_def, check_value_type_def, assignable_type_def,
          AllCaseEqs()])
  >> gvs[subscript_vtype_def, AllCaseEqs()]
QED

Theorem typed_type_builtin_form:
  type_builtin_result_ok tenv tb ty target (MAP expr_type es) /\
  well_typed_type_builtin_args tb target (MAP expr_type es) /\
  well_formed_type tenv ty /\
  (!bt. result_ok (BaseT bt)) /\
  (!t. supported_numeric_type t ==> result_ok t) /\
  (!s t. valid_conversion s t ==> result_ok t) /\
  (assignable_type tenv ty ==> supported_place_type tops ty /\ result_ok ty) ==>
  supported_type_builtin_form tops ty tb target es /\ result_ok ty
Proof
  strip_tac >>
  `(tb = MaxValue \/ tb = MinValue) ==> supported_numeric_type ty` by
    metis_tac[well_typed_max_min_value_supported] >>
  drule well_typed_type_builtin_args_arity >>
  Cases_on `tb` >> simp[] >> strip_tac >>
  gvs[LENGTH_EQ_NUM_compute, supported_type_builtin_form_def,
      type_builtin_result_ok_def, well_typed_type_builtin_args_def,
      supported_value_type_def]
  >~ [`abi_encode_size_ok`] >- (Cases_on `es` >> gvs[])
  >> metis_tac[]
QED

Theorem supported_place_type_tuple_el:
  supported_place_type tops (TupleT tys) /\ n < LENGTH tys ==>
  supported_place_type tops (EL n tys)
Proof
  rw[supported_place_type_def] >>
  qpat_x_assum `supported_nested_type _ _ _ (TupleT _)` mp_tac >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def, EVERY_EL]
QED
