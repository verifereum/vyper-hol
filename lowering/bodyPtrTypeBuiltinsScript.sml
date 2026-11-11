(*
 * Type builtins but abi_encode and abi_decode: empty, bounds, convert, extract32.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   type_builtin_expr_ptr_ok
 *)
Theory bodyPtrTypeBuiltins
Ancestors
  bodyPtrTypeBuiltinsWordCases bodyPtrSignedConvertConvertEntry
  bodyPtrTypeBuiltinsResidual bodyPtrTypeBuiltinsConvertWidened
  bodyPtrTypeBuiltinsSeamConvert bodyPtrTypeBuiltinsSeamEmpty
  bodyPtrTypeBuiltinsSeamExtract32 exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem type_builtin_expr_ptr_ok:
  !cx v11 tb typ es.
    (tb = Empty \/ tb = MaxValue \/ tb = MinValue \/ tb = Epsilon \/
     tb = Convert \/ tb = Extract32) /\
    (type_builtin_args_length_ok tb (LENGTH es) ==> body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (TypeBuiltin v11 tb typ es)
Proof
  rpt gen_tac >> strip_tac >> gvs[]
  >- (Cases_on `is_word_type typ`
      >- (irule empty_word_body_expr_ptr_ok >> simp[]) >>
      irule empty_memory_body_expr_ptr_ok >> simp[])
  >- (irule bound_builtin_body_expr_ptr_ok >> simp[])
  >- (irule bound_builtin_body_expr_ptr_ok >> simp[])
  >- (irule bound_builtin_body_expr_ptr_ok >> simp[])
  >- (Cases_on `?e. es = [e] /\ is_bytestring_type (expr_type e) /\
                ((?n. typ = BaseT (IntT n)) \/ typ = BaseT DecimalT)`
      >- (irule signed_bytestring_convert_residual >> gvs[] >> metis_tac[]) >>
      Cases_on `LENGTH es = 1`
      >- (Cases_on `es` >> gvs[] >> (rename1 `[e1]` >>
          gvs[vyperContextTheory.type_builtin_args_length_ok_def] >>
          simp[body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
          Cases_on `(?a f cargs drv. e1 = Call a (IntCall f) cargs drv) /\
                    lowered_value_type cenv e1 <> expr_type e1`
          >- (qspecl_then [`cx`,`v11`,`typ`,`e1`] mp_tac
                body_convert_widened_call_arg_ptr >>
              impl_tac >- first_assum ACCEPT_TAC >>
              disch_then (qspecl_then
                [`d`,`PG`,`tops`,`ctx`,`func`,`cenv`,`env`,`ty`,`es`] mp_tac) >>
              impl_tac >- fs[] >> simp[]) >>
          qspecl_then [`cx`,`v11`,`typ`,`e1`] mp_tac convert_unwidened_ptr >>
          impl_tac >- first_assum ACCEPT_TAC >>
          disch_then (qspecl_then
            [`d`,`PG`,`tops`,`ctx`,`func`,`cenv`,`env`,`ty`,`es`] mp_tac) >>
          impl_tac >- fs[] >> simp[])) >>
      irule convert_arity_body_expr_ptr_ok >> simp[]) >>
  irule extract32_body_expr_ptr_ok >> simp[]
QED
