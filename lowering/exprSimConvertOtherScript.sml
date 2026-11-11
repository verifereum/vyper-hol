(*
 * Expression simulation: the conversions exprSimConvert does not cover: to or from decimal, address, bytesM, bytestrings and flags.
 *
 * compile_convert_other_case, the case lemma exprSimAggregates re-exports for compile_expr_sim
 * (exprSimMain): from exprs_case of the operands, expr_vv_case of the
 * builtin, for an operand that is not an internal call whose type widens
 * its callee's return type (bodySimExprCases' body_convert_widened_call_arg
 * covers that one).  It splits on the operand count and on which side is a
 * bytestring: convertScalar's leaf for word to word, exprSimConvertBytes'
 * for a bytestring target, exprSimConvertFromBytes' for a bytestring
 * source.  A malformed arity is ill-typed.
 *)

Theory exprSimConvertOther
Ancestors
  exprSimHypsDefs exprSimConvert vyperAST vyperTypeSystem exprSimDefs
  exprSimConvertScalar exprSimConvertBytes exprSimConvertFromBytes

Theorem compile_convert_arity_case:
  !nocalls ctx func cenv cx ann t args.
    LENGTH args <> 1 ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t args)
Proof
  rw[expr_vv_case_def] >>
  fs[expr_body_pre_def, well_typed_expr_def,
     well_typed_type_builtin_args_def]
QED

Theorem compile_convert_other_case:
  !nocalls ctx func cenv cx ann t args.
    exprs_case nocalls ctx func cenv cx args /\
    ~(?e1. args = [e1] /\ int_convert_pair (expr_type e1) t) /\
    (~nocalls ==> !e1 a f cargs d. args = [e1] /\ e1 = Call a (IntCall f) cargs d ==>
       lowered_value_type cenv e1 = expr_type e1) ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t args)
Proof
  rpt strip_tac >> Cases_on `?e1. args = [e1]`
  >- (gvs[] >> rw[expr_vv_case_def] >>
      `!a f cargs d. e1 = Call a (IntCall f) cargs d ==>
         lowered_value_type cenv e1 = expr_type e1` by
        (rpt strip_tac >> Cases_on `nocalls` >> gvs[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
      Cases_on `is_bytestring_type t`
      >- (`expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t [e1])`
            by (irule compile_convert_to_bytestring_case >> simp[]) >>
          metis_tac[expr_vv_case_def]) >>
      Cases_on `is_bytestring_type (expr_type e1)`
      >- (`expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t [e1])`
            by (irule compile_convert_from_bytestring_case >> simp[]) >>
          metis_tac[expr_vv_case_def]) >>
      `expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t [e1])`
        by (irule compile_convert_scalar_case >> simp[]) >>
      metis_tac[expr_vv_case_def]) >>
  irule compile_convert_arity_case >>
  gvs[listTheory.LENGTH_EQ_NUM_compute]
QED
