(* Generated GAS prefixes retain the same full-outcome execution. *)
Theory bodyFullRawCallGeneratedPrefix
Ancestors
  gasOutcomeFull fragGasOriginPtr fragGasOrigin fragGasMode fragGasPathMem
  gasExemptCert gasSummary gasSummaryCompose gasStorage
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState list

Theorem raw_call_exempt_generated_prefix[local]:
  gas_path_mem ctx func s0 n (OK s1) /\
  gas_exempt_cert T tops (ctx,func) source (es,s1) marks (err,ee) (leaf,target_end) ==>
  gas_exempt_cert T tops (ctx,func) source (es,s0)
    (REPLICATE n F ++ marks) (err,ee) (leaf,target_end)
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func) (return ()) (es,s0)
     (REPLICATE n F) (INL ()) es (OK s1)` by
    simp[gas_marked_exec_def, gas_marked_path_def, return_def] >>
  `gas_exempt_cert T tops (ctx,func) source (es with gas_obs := [],s1)
     marks (err,ee) (leaf,target_end)` by
    (drule gas_exempt_cert_start_gas_obs >> simp[]) >>
  drule gas_exempt_cert_bind_unit >>
  disch_then (qspecl_then [`tops`, `\u. source`] mp_tac) >>
  simp[vyperStateTheory.bind_return] >> metis_tac[]
QED

Theorem raw_call_generated_prefix_full:
  storage_trace_frame source /\ storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s0,G0,tn0) (REPLICATE n F) (OK s1,G1,tn1)) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s1,G1,tn1) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by metis_tac[storage_trace_domain_def] >>
  `gas_path_mem ctx func s0 n (OK s1)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `!marks. gas_explicit (REPLICATE n F ++ marks) s0.vs_gas_readings =
     gas_explicit marks s1.vs_gas_readings` by
    (drule gas_path_mem_ok_suffix >> simp[gas_explicit_append]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `REPLICATE n F ++ marks`
  >- (disj1_tac >> conj_tac >- gvs[gas_bad_storage_at_def] >>
      qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      `valid_horizon cx st0 H es.storage_trace` by metis_tac[] >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
        (qspec_then `H` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
      drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >> gvs[] >>
      rpt strip_tac >>
      `valid_horizon cx st0 H es.storage_trace` by
        (qpat_assum `!tail. source _ = _` (qspec_then `[]` assume_tac) >>
         drule_all storage_trace_frame_prefix >> strip_tac >>
         gvs[] >> drule valid_horizon_append >> simp[]) >>
      res_tac >> metis_tac[gas_origin_ptr_path_append]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
  conj_tac >- (irule raw_call_exempt_generated_prefix >> metis_tac[]) >>
  qexists_tac `H` >> conj_tac >- first_assum ACCEPT_TAC >>
  `valid_horizon cx st0 H es.storage_trace` by metis_tac[] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[]
QED
