(* Memory case of the body induction (bodyMemory's body_mem_mutual): raw_call
   with calldata. *)
Theory bodyMemRawCallCalldata
Ancestors
  bodyMemoryPreds bodyInvNoDalloca bodyPtrCallCalldata rawCallCalldataDalloca
  exprSimMemDefs exprSimHypsDefs vyperTypeSystem fragExec
  gasOutcome gasStorage vyperStorageTrace vyperStorageFootprint

Theorem body_raw_call_calldata_mem_case:
  !cx ty flags es v19.
    body_exprs_mem_ok cx es ==>
    body_expr_mem_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  rpt gen_tac >> strip_tac >>
  rw[body_expr_mem_ok_def] >>
  rename1 `expr_body_pre cenv cx env _ ss` >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `es <> []` by
    (strip_tac >> gvs[expr_body_pre_def, well_typed_expr_def]) >>
  rw[expr_sim_mem_def, expr_vv_sim_mem_def] >>
  (reverse (Cases_on `storage_trace_domain cx st0 ss.storage_trace`)
   >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
       irule gas_bad_storage_at_initial >>
       simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
            storage_trace_frame_read_result])) >>
  `stmt_state_rel (storage_trace_horizon ss.storage_trace)
     ctx func cenv cx ss s0` by
    (fs[storage_trace_domain_def] >> metis_tac[]) >>
  `ctx_has_dalloca ctx` suffices_by simp[] >>
  drule stmt_state_rel_dalloca >> disch_then irule
  >- (drule lower_value_compile_expr_split >> strip_tac >>
      `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
      drule_all compile_expr_raw_call_calldata_dalloca >> simp[]) >>
  drule_all compile_expr_raw_call_calldata_dalloca >> simp[]
QED
