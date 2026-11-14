(* Memory case of the body induction (bodyMemory's body_mem_mutual): raw_call
   with calldata. *)
Theory bodyMemRawCallCalldata
Ancestors
  bodyMemoryPreds bodyInvNoDalloca bodyPtrCallCalldata rawCallCalldataDalloca
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
  rename1 `gas_outcome _ _ _ _ _ _ (frame_es, s0) _ _` >>
  (reverse (Cases_on `?H0. valid_horizon cx st0 H0 frame_es.storage_trace`)
   >- (rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
       qexists_tac `[]` >> disj1_tac >>
       irule gasStorageTheory.gas_bad_storage_at_initial >>
       simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
            vyperStorageTraceTheory.evaluate_storage_trace_frame,
            vyperStorageTraceTheory.storage_trace_frame_read_result] >>
       fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
   pop_assum strip_assume_tac >>
   qpat_x_assum `!H. valid_horizon _ _ H frame_es.storage_trace ==> _`
     (qspec_then `H0` mp_tac) >> simp[] >> strip_tac >>
   `ctx_has_dalloca ctx` suffices_by simp[] >>
   irule (INST_TYPE [alpha |-> ``:256``] stmt_state_rel_dalloca) >>
   qexistsl_tac [`H0`, `cenv`, `cx`, `func`, `s0`, `frame_es`] >> simp[])
  >- (drule lower_value_compile_expr_split >> strip_tac >>
      `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
      drule_all compile_expr_raw_call_calldata_dalloca >> simp[]) >>
  drule_all compile_expr_raw_call_calldata_dalloca >> simp[]
QED
