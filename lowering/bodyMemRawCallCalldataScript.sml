(* Memory case of the body induction (bodyMemory's body_mem_mutual): raw_call
   with calldata. *)
Theory bodyMemRawCallCalldata
Ancestors
  bodyMemoryPreds bodyInvNoDalloca bodyPtrCallCalldata
  exprSimMemDefs exprSimHypsDefs vyperTypeSystem fragExec

Theorem body_raw_call_calldata_mem_case:
  !cx ty flags es v19.
    body_exprs_mem_ok cx es ==>
    body_expr_mem_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  rpt gen_tac >> strip_tac >>
  rw[body_expr_mem_ok_def] >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `es <> []` by
    (strip_tac >> gvs[expr_body_pre_def, well_typed_expr_def]) >>
  rw[expr_sim_mem_def, expr_vv_sim_mem_def] >>
  `ctx_has_dalloca ctx` suffices_by simp[] >>
  irule stmt_state_rel_dalloca >> first_assum (irule_at Any)
  >- (drule lower_value_compile_expr_split >> strip_tac >>
      `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
      drule_all compile_expr_raw_call_calldata_dalloca >> simp[]) >>
  drule_all compile_expr_raw_call_calldata_dalloca >> simp[]
QED
