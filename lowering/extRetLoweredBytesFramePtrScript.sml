Theory extRetLoweredBytesFramePtr
Ancestors
  extRetSignatureFramePtr exprLowering compileEnv vyperTypeSystem vyperAST typedCopyPtr

Theorem typed_lowered_value_bytestring:
  well_typed_expr env e /\
  (!id sig. FLOOKUP env.fn_sigs id = SOME sig ==>
    cenv.ce_func_return_type (nsid_to_string id) = sig.ret_ty) /\
  is_bytestring_type (expr_type e) ==>
  is_bytestring_type (lowered_value_type cenv e)
Proof
  strip_tac >> Cases_on `e` >>
  gvs[lowered_value_type_def, expr_type_def]
  >~ [`Literal t l`]
  >- (Cases_on `t` >> gvs[is_bytestring_type_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[is_bytestring_type_def] >>
      Cases_on `l` >> simp[lowered_value_type_def, expr_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[lowered_value_type_def, expr_type_def, is_bytestring_type_def]) >>
  all_tac
  >~ [`TypeBuiltin ty builtin tys args`]
  >- (Cases_on `builtin` >>
      gvs[lowered_value_type_def, expr_type_def, is_bytestring_type_def]) >>
  rename1 `Call ty target args drv` >> Cases_on `target` >>
  gvs[lowered_value_type_def, expr_type_def] >>
  PairCases_on `p` >> gvs[well_typed_expr_def] >>
  first_x_assum drule >> disch_then SUBST1_TAC >>
  metis_tac[type_widens_to_def, arg_type_fits_bytestring_source]
QED

Theorem typed_dynamic_bytes_return_source:
  IS_SOME (type_stmt env (BaseT (BytesT (Dynamic n))) (Return (SOME e))) ==>
  well_typed_expr env e /\ is_bytestring_type (expr_type e)
Proof
  simp[type_stmt_return_some_iff] >> strip_tac >> simp[] >>
  irule arg_type_fits_bytestring_source >>
  qexists_tac `BaseT (BytesT (Dynamic n))` >>
  gvs[type_widens_to_def, is_bytestring_type_def, arg_type_fits_def]
QED
