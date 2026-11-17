(* gas_outcome_full_zero_prefix for a zero-reading prefix whose origin path
   holds only on the horizons valid for the starting storage trace. *)
Theory gasOutcomeFullGuarded
Ancestors
  gasOutcomeFullStmts gasOutcomeFullCompose gasOutcomeFull fragGasOriginPtr
  fragGasOrigin fragGasMode fragGasPath fragExec gasOutcome gasExemptCert
  gasSummary gasSummaryCompose gasStorage fragGasPathMem stmtSimExpr
  stmtSimIfProps bodyDeclMemoryCompose
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState list

Theorem origin_ptr_path_zero_prefix[local]:
  gas_origin_ptr_path cx st [] (OK s1, G1, tn1) /\
  gas_origin_ptr_path cx (s1, G1, tn1) marks out ==>
  gas_origin_ptr_path cx st marks out
Proof
  PairCases_on `out` >> strip_tac >>
  qpat_x_assum `gas_origin_ptr_path _ _ [] _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  simp[] >> disch_then drule >> simp[]
QED

(* A storage-trace-framed source only appends to the trace. *)
Theorem storage_trace_frame_prefix[local]:
  storage_trace_frame source /\ source (es with gas_obs := g) = (res, ee) ==>
  ?X. ee.storage_trace = es.storage_trace ++ X
Proof
  strip_tac >>
  `(es with gas_obs := g) with storage_trace := es.storage_trace =
     es with gas_obs := g` by simp[evaluation_state_component_equality] >>
  qpat_x_assum `storage_trace_frame _`
    (mp_tac o Q.SPECL [`es with gas_obs := g`, `es.storage_trace`] o
     REWRITE_RULE [storage_trace_frame_def]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `source ((es with gas_obs := g) with storage_trace := [])` >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem gas_outcome_full_zero_prefix_guarded:
  storage_trace_frame source /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s0, G0, tn0) [] (OK s1, G1, tn1)) /\
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s1, G1, tn1) Q R ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  `gas_path_mem ctx func s0 0 (OK s1)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (drule gas_path_mem_ok_suffix >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac >- gvs[gas_bad_storage_at_def] >>
      qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      `valid_horizon cx st0 H es.storage_trace` by
        (qpat_x_assum `storage_trace_domain _ _ _ ==> _` irule >>
         first_assum ACCEPT_TAC) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _`
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
      res_tac >> simp[] >> metis_tac[origin_ptr_path_zero_prefix]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`,
                `finish'`] >>
  conj_tac >- (irule gas_exempt_cert_zero_prefix_mem >> metis_tac[]) >>
  qexists_tac `H` >> conj_tac >- first_assum ACCEPT_TAC >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_x_assum `storage_trace_domain _ _ _ ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[]
QED
