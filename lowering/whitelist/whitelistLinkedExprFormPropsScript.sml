Theory whitelistLinkedExprFormProps
Ancestors
  vyperAST vyperImportRefs vyperTypeSystem vyperTypeContract whitelistCheckerExprs
  whitelistCheckerTypes supportedExprForms supportedGetterProps supportedTypes
  list rich_list
  whitelistExprTypeProps whitelistHashmapValueProps

Theorem linked_builtin_form:
  well_typed_builtin_app ty bi (MAP expr_type es) /\
  (!s b. bi = MakeArray s b ==> supported_place_type tops ty) ==>
  supported_builtin_form tops ty bi es /\ checker_agg_ok tops ty
Proof
  strip_tac >> Cases_on `?s b. bi = MakeArray s b`
  >- (gvs[] >> Cases_on `s` >> Cases_on `b` >>
      gvs[supported_builtin_form_def, well_typed_builtin_app_def,
          checker_agg_ok_def]) >>
  irule well_typed_builtin_supported_form >> metis_tac[]
QED

Theorem imported_expr_refs_type:
  imported_expr_refs_ok e ==> imported_type_refs_ok (expr_type e)
Proof
  Cases_on `e` >> simp[imported_expr_refs_ok_def, expr_type_def]
QED

Theorem linked_type_builtin_form:
  type_builtin_result_ok tenv tb ty target (MAP expr_type es) /\
  well_typed_type_builtin_args tb target (MAP expr_type es) /\
  well_formed_type tenv ty /\
  (assignable_type tenv ty ==> supported_place_type tops ty) ==>
  supported_type_builtin_form tops ty tb target es /\ checker_agg_ok tops ty
Proof
  strip_tac >> irule (Q.INST [`tenv` |-> `tenv`] typed_type_builtin_form) >>
  simp[checker_agg_ok_def] >> conj_tac
  >- (rpt gen_tac >> disch_then (mp_tac o MATCH_MP valid_conversion_nonaggregate) >>
      Cases_on `t` >> simp[]) >>
  conj_tac
  >- (Cases >> simp[supported_numeric_type_def, supported_integer_type_def]) >>
  qexists_tac `tenv` >> simp[] >> metis_tac[]
QED

Theorem linked_subscript_value:
  checker_agg_ok tops (expr_type be) /\ subscript_type_ok (expr_type be) key ty /\
  (~qualified_place_root be ==>
   supported_place_info tops be = ValPT (expr_type be)) ==>
  supported_subscript_place tops be /\ supported_place_type tops ty
Proof
  strip_tac >> Cases_on `expr_type be` >>
  gvs[subscript_type_ok_def, checker_agg_ok_def]
  >~ [`ArrayT`] >-
    (Cases_on `qualified_place_root be` >> gvs[supported_subscript_place_def] >>
     irule supported_place_array_element >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `qualified_place_root be` >> gvs[supported_subscript_place_def]) >>
  Cases_on `key` >> gvs[] >> BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  metis_tac[supported_place_type_tuple_el]
QED

Theorem checked_value_type_supported_hashmap:
  (!ty. assignable_type tenv ty ==> supported_place_type tops ty) ==>
  !v. check_value_type tenv v ==> supported_hashmap_value tops v
Proof
  rpt strip_tac >>
  mp_tac (Q.INST [`imported_only` |-> `F`] checked_hashmap_value_supported) >>
  impl_tac >- metis_tac[checker_hashmap_key_supported] >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED
