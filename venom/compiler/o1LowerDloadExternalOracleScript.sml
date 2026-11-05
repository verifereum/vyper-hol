(* Masked oracle observations, independent of relocated output buffers. *)
Theory o1LowerDloadExternalOracle
Ancestors ptrDiscipline venomCallOracleDefs extCallOracle venomState list

Theorem ld_take_outcome_masked_observation:
  request_agree_except D rq1 rq2 ==>
  (FST (take_outcome rq1 os)).co_success =
    (FST (take_outcome rq2 os)).co_success /\
  (FST (take_outcome rq1 os)).co_returnData =
    (FST (take_outcome rq2 os)).co_returnData /\
  SND (take_outcome rq1 os) = SND (take_outcome rq2 os)
Proof
  strip_tac >>
  `rq1.cr_target = rq2.cr_target /\ rq1.cr_value = rq2.cr_value /\
   rq1.cr_kind = rq2.cr_kind /\ rq1.cr_data = rq2.cr_data` by
    (fs[request_agree_except_def, call_request_component_equality]) >>
  `computed_precompile rq1 = computed_precompile rq2` by
    simp[computed_precompile_def] >>
  Cases_on `os` >> simp[take_outcome_def, failed_outcome_def] >>
  Cases_on `computed_precompile rq2` >> simp[] >>
  Cases_on `precompile_result rq2.cr_target rq2.cr_data`
  >- simp[failed_outcome_def] >>
  rename1 `precompile_result _ _ = SOME x` >> Cases_on `x` >>
  simp[failed_outcome_def] >> IF_CASES_TAC >> simp[failed_outcome_def]
QED

Theorem ld_consume_call_outcome_masked_observation:
  request_agree_except D rq1 rq2 /\ s.vs_outcomes = t.vs_outcomes /\
  LIST_REL (request_agree_except D) s.vs_requests t.vs_requests /\
  consume_call_outcome rq1 ro1 rs1 s = (w1,s1) /\
  consume_call_outcome rq2 ro2 rs2 t = (w2,t1) ==>
  w1 = w2 /\ s1.vs_outcomes = t1.vs_outcomes /\
  s1.vs_returndata = t1.vs_returndata /\
  LIST_REL (request_agree_except D) s1.vs_requests t1.vs_requests
Proof
  strip_tac >>
  drule ld_take_outcome_masked_observation >>
  disch_then (qspec_then `t.vs_outcomes` strip_assume_tac) >>
  `computed_precompile rq1 = computed_precompile rq2` by
    fs[request_agree_except_def, call_request_component_equality,
       computed_precompile_def] >>
  gvs[consume_call_outcome_eq, record_request_def] >>
  Cases_on `computed_precompile rq2` >> simp[LIST_REL_APPEND]
QED
