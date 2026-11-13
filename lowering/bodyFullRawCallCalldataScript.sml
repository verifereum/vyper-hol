(*
 * raw_call with calldata over the finite-horizon joint judgment: vacuous.
 * Its lowering emits a DALLOCA into the function, and the joint judgments
 * assume the context has none.
 *
 * TOP-LEVEL:
 *   raw_call_calldata_expr_full_ok -- the raw_call-with-calldata case
 *)
Theory bodyFullRawCallCalldata
Ancestors
  bodyFullPreds bodySimFull bodyPtrCallCalldata exprSimHypsDefs fragExec
  ptrDiscipline exprLowering vyperAST list

val _ = Parse.hide "body";

Theorem raw_call_calldata_expr_full_ok:
  !cx ty flags es v19.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  rw[body_expr_full_ok_def] >>
  `es <> []` by (strip_tac >> gvs[expr_body_pre_def, well_typed_expr_def]) >>
  rw[expr_sim_full_def, expr_vv_sim_full_def] >>
  qpat_x_assum `~ctx_has_dalloca _` mp_tac >>
  simp[ctx_has_dalloca_def, EXISTS_MEM] >>
  first_assum (irule_at Any) >>
  simp[GSYM EXISTS_MEM]
  >- (drule lower_value_compile_expr_split >> strip_tac >>
      `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
      drule_all compile_expr_raw_call_calldata_dalloca >> simp[]) >>
  drule_all compile_expr_raw_call_calldata_dalloca >> simp[]
QED
