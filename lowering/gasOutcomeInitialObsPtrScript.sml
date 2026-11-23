(* Initial source observations are overwritten by marked execution.  Keep
   certificate induction here, not in consumers of pointer outcomes. *)
Theory gasOutcomeInitialObsPtr
Ancestors gasExemptCert gasExemptOrigin gasNormalPrefix gasSummary
  gasSummaryComposePtr fragGasPathPtr loweringPosts exprSimWordArgs
  vyperState vyperInterpreter
Libs monadsyntax

Theorem gas_marked_exec_initial_obs:
  gas_marked_exec memory p source (es with gas_obs := gs,s) marks res ee r <=>
  gas_marked_exec memory p source (es,s) marks res ee r
Proof
  Cases_on `p` >> simp[gas_marked_exec_def]
QED

Theorem expr_post_initial_obs:
  expr_post H ctx fn cenv cx e (es with gas_obs := gs) sa sb s0 ee v op t <=>
  expr_post H ctx fn cenv cx e es sa sb s0 ee v op t
Proof
  simp[expr_post_def, locals_kept_def, popped_kept_def]
QED

Theorem gas_value_prefix_initial_obs:
  gas_value_prefix H memory p te code (es with gas_obs := gs,s) marks result <=>
  gas_value_prefix H memory p te code (es,s) marks result
Proof
  PairCases_on `p` >> PairCases_on `te` >> PairCases_on `code` >>
  PairCases_on `result` >>
  `storage_well_formed_on p3 (es with gas_obs := gs) (FST H) <=>
   storage_well_formed_on p3 es (FST H)` by
    (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
     simp[]) >>
  simp[gas_value_prefix_def, stmt_state_rel_gas_obs,
       gas_marked_exec_initial_obs, expr_post_initial_obs]
QED

Theorem gas_exempt_origin_initial_obs:
  gas_exempt_origin memory tops p source (es with gas_obs := gs,s) marks out t <=>
  gas_exempt_origin memory tops p source (es,s) marks out t
Proof
  Cases_on `p` >> Cases_on `out` >>
  simp[gas_exempt_origin_def, gas_value_prefix_initial_obs]
QED

Theorem gas_exempt_cert_initial_obs_forward:
  !memory tops p source start marks out endpoint.
    gas_exempt_cert memory tops p source start marks out endpoint ==>
    !gs. gas_exempt_cert memory tops p source
      ((FST start) with gas_obs := gs,SND start) marks out endpoint
Proof
  ACCEPT_TAC gas_exempt_cert_start_gas_obs
QED

Theorem gas_exempt_cert_initial_obs:
  gas_exempt_cert memory tops p source (es with gas_obs := gs,s) marks out endpoint <=>
  gas_exempt_cert memory tops p source (es,s) marks out endpoint
Proof
  eq_tac >> strip_tac >> drule gas_exempt_cert_initial_obs_forward
  >- (disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[]) >>
  disch_then (qspec_then `gs` mp_tac) >> simp[]
QED

Theorem gas_summary_ptr_at_initial_obs:
  gas_summary_ptr_at D p PG cx st0 marks source
    (es with gas_obs := gs,s,G,tn) Q R <=>
  gas_summary_ptr_at D p PG cx st0 marks source (es,s,G,tn) Q R
Proof
  Cases_on `p` >> simp[gas_summary_ptr_at_def]
QED

Theorem gas_outcome_ptr_initial_obs:
  gas_outcome_ptr D tops p PG cx st0 source (es with gas_obs := gs,s,G,tn)
    Q R <=>
  gas_outcome_ptr D tops p PG cx st0 source (es,s,G,tn) Q R
Proof
  Cases_on `p` >> simp[gas_outcome_ptr_def, gasStorageTheory.gas_bad_storage_at_def,
    gas_summary_ptr_at_initial_obs, gas_exempt_cert_initial_obs]
QED
