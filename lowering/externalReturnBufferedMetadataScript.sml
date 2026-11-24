Theory externalReturnBufferedMetadata
Ancestors
  retAbiPlanProps compileVyper exprLowering compileEnv
  vyperABI vyperTypeSystem vyperTypeArgFits
  exprSimAbiEncodeArgsPhysicalCapacity loweringHalt stmtLowering

Theorem return_source_abi_fields:
  (update_cenv_ret_abi ce ty).ce_ret_enc_info =
    type_to_abi_enc_info ce.ce_struct_fields ce
      (if needs_external_call_wrap ty /\ is_abi_dynamic ce.ce_struct_fields ty
       then TupleT [ty] else ty) /\
  (update_cenv_ret_abi ce ty).ce_max_return_size =
    abi_size_bound ce.ce_struct_fields
      (if needs_external_call_wrap ty /\ is_abi_dynamic ce.ce_struct_fields ty
       then TupleT [ty] else ty)
Proof
  simp[compileVyperTheory.update_cenv_ret_abi_def, external_return_needs_wrap_eq] >>
  IF_CASES_TAC >> gvs[] >>
  simp[Once exprLoweringTheory.type_to_abi_enc_info_def,
       Once abi_size_bound_def, is_abi_dynamic_def, abi_embedded_static_size_def]
QED

Theorem return_wrap_fits:
  !t u. arg_type_fits t u ==> needs_external_call_wrap t = needs_external_call_wrap u
Proof
  Cases >> Cases >> simp[arg_type_fits_def, vyperABITheory.needs_external_call_wrap_def] >>
  metis_tac[vyperTypeArgFitsTheory.arg_types_fit_LENGTH]
QED

Theorem return_abi_size_fits:
  arg_type_fits t u /\ ce.ce_struct_fields = ce'.ce_struct_fields ==>
  (update_cenv_ret_abi ce t).ce_max_return_size <=
    (update_cenv_ret_abi ce' u).ce_max_return_size
Proof
  strip_tac >> drule return_wrap_fits >> strip_tac >>
  `is_abi_dynamic ce'.ce_struct_fields t = is_abi_dynamic ce'.ce_struct_fields u` by
    metis_tac[cj 1 abi_args_fits_static_shape] >>
  `arg_type_fits (TupleT [t]) (TupleT [u])` by simp[arg_type_fits_def] >>
  asm_simp_tac bool_ss [return_source_abi_fields] >> IF_CASES_TAC >>
  metis_tac[cj 1 abi_args_fits_size_bound]
QED

Theorem valued_return_compiler_transient:
  (nr /\ ~iv ==> ut) ==>
  compile_external_return rv prim raw ei msz nr nkey ut iv =
  compile_external_return rv prim raw ei msz nr nkey T iv
Proof
  strip_tac >> Cases_on `nr /\ ~iv`
  >- fs[] >>
  `nr ==> iv` by (Cases_on `nr` >> fs[]) >>
  PURE_REWRITE_TAC [compile_external_return_def] >>
  simp[optional_unlock_view]
QED
