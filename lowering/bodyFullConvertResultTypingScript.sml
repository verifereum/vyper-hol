(* Pure semantic typing boundary for successful scalar conversions. *)
Theory bodyFullConvertResultTyping
Ancestors
  exprSimConvert vyperTypeConversions vyperTypeSystem vyperValueOperation
  vyperValue vyperAST compileEnv

Theorem scalar_convert_result_typed:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  evaluate_type (get_tenv cx) src = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  convert_result cx src dst v = INL vout ==> value_has_type tout vout
Proof
  strip_tac >> irule valid_conversion_success_type >>
  qexistsl [`cx`, `tv`, `src`, `dst`, `v`] >>
  gvs[convert_result_def, vyperContextTheory.evaluate_type_builtin_def, AllCaseEqs()]
QED
