(* Internal wrappers preserve all previously emitted compiler code. *)
Theory entryInternalAppend
Ancestors
  entryCompileIntervals moduleLowering compileEnv context fragExec
  stmtLoweringMono abiDecoderAppend

Theorem cs_appends_fixed_region[local]:
  cs_appends (compile_fixed_region_with_id n)
Proof
  simp[compile_fixed_region_with_id_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_prims, cs_appends_return]),
    gen_tac, irule cs_appends_bind, irule cs_appends_ignore_bind, conj_tac])
QED

Theorem cs_appends_internal_param_decls[local]:
  !xs idx. cs_appends (compile_internal_param_decls xs idx)
Proof
  Induct >> simp[compile_internal_param_decls_def, cs_appends_return] >>
  gen_tac >> PairCases_on `h` >> simp[compile_internal_param_decls_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_emit_helpers, cs_appends_return]),
    gen_tac, irule cs_appends_bind, irule cs_appends_ignore_bind, conj_tac])
QED

Theorem cs_appends_materialize_internal_params[local]:
  !xs ce. cs_appends (materialize_internal_params ce xs)
Proof
  Induct >> simp[materialize_internal_params_def, cs_appends_return] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[materialize_internal_params_def] >> IF_CASES_TAC >> simp[] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_emit_helpers, cs_appends_return]),
    gen_tac, irule cs_appends_bind, irule cs_appends_ignore_bind, conj_tac])
QED

Theorem cs_appends_internal_function:
  cs_appends (compile_internal_function ce params has_ret nr key tr view
    ctor imm stmts rt)
Proof
  simp[compile_internal_function_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_emit_helpers, cs_appends_return,
    cs_appends_internal_param_decls, cs_appends_materialize_internal_params,
    cs_appends_fixed_region, cs_appends_abi_alloc_buffer,
    cs_appends_nonreentrant, cs_appends_stmts, cs_appends_comp_get]),
    gen_tac, irule cs_appends_bind,
    irule cs_appends_ignore_bind, conj_tac, IF_CASES_TAC]) >>
  Cases_on `rt` >> simp[cs_appends_return, cs_appends_emit_helpers] >>
  IF_CASES_TAC >> simp[cs_appends_return] >>
  irule cs_appends_ignore_bind >>
  simp[cs_appends_abi_alloc_buffer, cs_appends_return]
QED

Theorem cs_appends_internal_fn_bodies:
  !xs. cs_appends (compile_internal_fn_bodies xs)
Proof
  Induct >> simp[compile_internal_fn_bodies_def, cs_appends_return] >>
  gen_tac >> PairCases_on `h` >> simp[compile_internal_fn_bodies_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_prims,
    cs_appends_internal_function]), gen_tac, irule cs_appends_bind,
    irule cs_appends_ignore_bind, conj_tac])
QED
