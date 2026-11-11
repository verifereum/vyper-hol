(* Unrecorded computed precompiles never observe masked shared inputs. *)
Theory o1LowerDloadPrecompileEffects
Ancestors
  o1LowerDloadExternalEffects o1LowerDloadShared venomCallOracleDefs
  extCallOracle venomState ptrDiscipline list

Theorem ld_consume_precompile_shared:
  ld_shared_agree D A tn s t /\
  computed_precompile rq1 /\ computed_precompile rq2 /\
  rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq1 ro1 rs1 s = (w1,s1) /\
  consume_call_outcome rq2 ro2 rs2 t = (w2,t1) ==>
  w1 = w2 /\ s1.vs_returndata = t1.vs_returndata /\
  s1.vs_accounts = s.vs_accounts /\ t1.vs_accounts = t.vs_accounts /\
  s1.vs_transient = s.vs_transient /\ t1.vs_transient = t.vs_transient /\
  ld_shared_agree D A tn s1 t1
Proof
  strip_tac >>
  `s.vs_outcomes = t.vs_outcomes` by fs[ld_shared_agree_def] >>
  Cases_on `t.vs_outcomes` >>
  gvs[consume_call_outcome_eq, take_outcome_def, record_request_def,
      adopt_outcome_def, adopt_outcome_deletions_def, failed_outcome_def,
      ld_shared_agree_def] >>
  Cases_on `precompile_result rq2.cr_target rq2.cr_data`
  >- gvs[adopt_outcome_def, adopt_outcome_deletions_def, failed_outcome_def] >>
  rename1 `precompile_result _ _ = SOME x` >> Cases_on `x` >>
  gvs[adopt_outcome_def, adopt_outcome_deletions_def, failed_outcome_def] >>
  Cases_on `h.co_success` >>
  gvs[adopt_outcome_def, adopt_outcome_deletions_def, failed_outcome_def]
QED
