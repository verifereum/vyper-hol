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
  expr_post ctx fn cenv cx e (es with gas_obs := gs) sa sb s0 ee v op t <=>
  expr_post ctx fn cenv cx e es sa sb s0 ee v op t
Proof
  simp[expr_post_def, locals_kept_def]
QED

Theorem gas_value_prefix_initial_obs:
  gas_value_prefix memory p te code (es with gas_obs := gs,s) marks result <=>
  gas_value_prefix memory p te code (es,s) marks result
Proof
  PairCases_on `p` >> PairCases_on `te` >> PairCases_on `code` >>
  PairCases_on `result` >>
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
  ho_match_mp_tac gas_exempt_cert_ind >> rpt conj_tac
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      irule (cj 1 gas_exempt_cert_rules) >>
      simp[gas_exempt_origin_initial_obs])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 2 gas_exempt_cert_rules, gas_marked_exec_initial_obs])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 3 gas_exempt_cert_rules])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 4 gas_exempt_cert_rules, gas_marked_exec_initial_obs])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 5 gas_exempt_cert_rules])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 6 gas_exempt_cert_rules, gas_marked_exec_initial_obs])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 7 gas_exempt_cert_rules])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 8 gas_exempt_cert_rules, gas_marked_exec_initial_obs])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 9 gas_exempt_cert_rules])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 10 gas_exempt_cert_rules, gas_marked_exec_initial_obs])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 11 gas_exempt_cert_rules])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 12 gas_exempt_cert_rules, gas_marked_exec_initial_obs])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 13 gas_exempt_cert_rules])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 14 gas_exempt_cert_rules, gas_marked_exec_initial_obs])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 15 gas_exempt_cert_rules])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      irule (cj 16 gas_exempt_cert_rules) >> qexists_tac `mid` >> simp[])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      irule (cj 17 gas_exempt_cert_rules) >> qexists_tac `mid` >> simp[])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      irule (cj 18 gas_exempt_cert_rules) >> simp[])
  >- (rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
      metis_tac[cj 19 gas_exempt_cert_rules]) >>
  rpt gen_tac >> simp[] >> strip_tac >> gen_tac >>
  metis_tac[cj 20 gas_exempt_cert_rules]
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
  gas_summary_ptr_at D p PG marks source (es with gas_obs := gs,s,G,tn) Q R <=>
  gas_summary_ptr_at D p PG marks source (es,s,G,tn) Q R
Proof
  Cases_on `p` >> simp[gas_summary_ptr_at_def]
QED

Theorem gas_outcome_ptr_initial_obs:
  gas_outcome_ptr D tops p PG source (es with gas_obs := gs,s,G,tn) Q R <=>
  gas_outcome_ptr D tops p PG source (es,s,G,tn) Q R
Proof
  Cases_on `p` >> simp[gas_outcome_ptr_def,
    gas_summary_ptr_at_initial_obs, gas_exempt_cert_initial_obs]
QED
