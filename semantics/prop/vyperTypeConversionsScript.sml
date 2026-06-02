(*
 * Conversion, max/min value, and extract32 typing lemmas.
 *)

Theory vyperTypeConversions
Ancestors
  list rich_list arithmetic finite_map option pair words byte
  vyperAST vyperValue vyperValueOperation vyperMisc vyperContext
  vyperTyping vyperArith vyperTypeSystem vyperTypeValues vyperTypeDefaults
Libs
  wordsLib

Theorem bounded_decimal_op_no_type_error[simp]:
  bounded_decimal_op x <> INR (TypeError s)
Proof
  rw[bounded_decimal_op_def]
QED

Theorem valid_conversion_no_type_error:
  valid_conversion from_ty to_ty /\
  evaluate_type (get_tenv cx) from_ty = SOME from_tv /\
  evaluate_type (get_tenv cx) to_ty = SOME to_tv /\
  value_has_type from_tv v ==>
  !msg. evaluate_type_builtin cx Convert to_ty [v] <> INR (TypeError msg)
Proof
  rpt strip_tac >>
  gvs[evaluate_type_builtin_def] >>
  Cases_on`from_ty` >> Cases_on`to_ty` >>
  gvs[valid_conversion_def, evaluate_type_def, AllCaseEqs()] >>
  gvs[oneline value_has_type_def, evaluate_convert_def] >>
  reverse(Cases_on`∃i. v = IntV i`)
  >- (Cases_on`v` >> gvs[])
  >> gvs[evaluate_convert_def]
  >> Cases_on`v` >> gvs[evaluate_convert_def]
QED

Theorem evaluate_max_value_well_typed:
  !typ tv. evaluate_type tenv typ = SOME tv /\
           evaluate_max_value typ = INL v ==>
           value_has_type tv v
Proof
  Cases >> simp[evaluate_max_value_def, evaluate_type_def] >>
  Cases_on `b` >> simp[evaluate_max_value_def, evaluate_type_def,
                        AllCaseEqs(), value_has_type_def,
                        within_int_bound_def] >>
  rpt strip_tac >> gvs[value_has_type_def, within_int_bound_def] >>
  `1 <= 2 ** n /\ 1 <= 2 ** (n - 1)` by simp[ONE_LE_EXP] >>
  simp[integerTheory.INT_SUB, integerTheory.NUM_OF_INT]
QED

Theorem evaluate_min_value_well_typed:
  !typ tv. evaluate_type tenv typ = SOME tv /\
           evaluate_min_value typ = INL v ==>
           value_has_type tv v
Proof
  Cases >> simp[evaluate_min_value_def, evaluate_type_def] >>
  Cases_on `b` >> simp[evaluate_min_value_def, evaluate_type_def,
                        AllCaseEqs(), value_has_type_def,
                        within_int_bound_def]
QED

Theorem evaluate_convert_well_typed:
  !tenv v typ v' tv.
    evaluate_convert tenv v typ = INL v' /\
    evaluate_type tenv typ = SOME tv ==>
    value_has_type tv v'
Proof
  ho_match_mp_tac evaluate_convert_ind >>
  rpt strip_tac >>
  gvs[evaluate_convert_def, AllCaseEqs(), evaluate_type_def,
      value_has_type_def, bounded_decimal_op_def,
      within_int_bound_def, compatible_bound_def] >>
  gvs[LENGTH_TAKE, listTheory.PAD_RIGHT,
      LENGTH_word_to_bytes, word_to_bytes_be_def] >>
  TRY (Cases_on `b` >> gvs[ONE_LT_EXP])
QED

Theorem evaluate_extract32_well_typed:
  !bs n bt v tenv tv.
    evaluate_extract32 bs n bt = INL v /\
    evaluate_type tenv (BaseT bt) = SOME tv ==>
    value_has_type tv v
Proof
  rpt strip_tac >>
  gvs[evaluate_extract32_def, AllCaseEqs()] >>
  TRY (drule evaluate_convert_well_typed >>
       disch_then irule >>
       gvs[evaluate_type_def, AllCaseEqs()] >> NO_TAC) >>
  gvs[value_has_type_def, evaluate_type_def, AllCaseEqs(),
      LENGTH_TAKE, LENGTH_DROP]
QED

Theorem valid_conversion_success_type:
  valid_conversion from_ty to_ty /\
  evaluate_type (get_tenv cx) from_ty = SOME from_tv /\
  evaluate_type (get_tenv cx) to_ty = SOME to_tv /\
  value_has_type from_tv v /\
  evaluate_type_builtin cx Convert to_ty [v] = INL v' ==>
  value_has_type to_tv v'
Proof
  rw[evaluate_type_builtin_def] >>
  drule_all evaluate_convert_well_typed >> simp[]
QED
