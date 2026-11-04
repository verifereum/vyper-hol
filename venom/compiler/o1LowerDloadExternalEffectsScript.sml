(* Shared adoption and return-buffer transport boundaries. *)
Theory o1LowerDloadExternalEffects
Ancestors o1LowerDloadExternalOracle o1LowerDloadShared
  o1LowerDloadRangeTransport venomCallOracleDefs extCallOracle
  ptrDiscipline venomState finite_map list pred_set

Theorem ld_consume_call_outcome_shared:
  ld_shared_agree D A tn s t /\ request_agree_except D rq1 rq2 /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq1 ro1 rs1 s = (w1,s1) /\
  consume_call_outcome rq2 ro2 rs2 t = (w2,t1) ==>
  ld_shared_agree D A
    (tn with <|t_stor := if s1.vs_accounts <> s.vs_accounts then {} else tn.t_stor;
               t_trans := if s1.vs_transient <> s.vs_transient then {} else tn.t_trans|>)
    s1 t1
Proof
  strip_tac >>
  `rq1.cr_target = rq2.cr_target /\ rq1.cr_value = rq2.cr_value /\
   rq1.cr_data = rq2.cr_data /\ rq1.cr_static = rq2.cr_static` by
    fs[request_agree_except_def, call_request_component_equality] >>
  `computed_precompile rq1 = computed_precompile rq2` by
    simp[computed_precompile_def] >>
  `s.vs_outcomes = t.vs_outcomes` by fs[ld_shared_agree_def] >>
  Cases_on `computed_precompile rq2`
  >- (Cases_on `precompile_result rq2.cr_target rq2.cr_data` >>
      gvs[consume_call_outcome_eq, take_outcome_def, record_request_def,
          ld_shared_agree_def] >>
      rename1 `precompile_result _ _ = SOME x` >> Cases_on `x` >>
      gvs[consume_call_outcome_eq, take_outcome_def, record_request_def,
          adopt_outcome_def, adopt_outcome_deletions_def, failed_outcome_def,
          ld_shared_agree_def]) >>
  Cases_on `t.vs_outcomes` >>
  gvs[consume_call_outcome_eq, take_outcome_def, record_request_def,
      adopt_outcome_def, adopt_outcome_deletions_def, failed_outcome_def] >>
  gvs[ld_shared_agree_def, LIST_REL_APPEND] >>
  rename1 `h.co_success` >>
  Cases_on `h.co_success /\ ~rq2.cr_static` >>
  gvs[] >>
  simp[word_agree_except_def] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[word_agree_except_def]
QED
