Theory lowerDloadOracleAdoption
Ancestors
  lowerDloadOracleSelection lowerDloadSharedState extCallOracle ptrDiscipline

(* Neither histories nor snapshot records have to agree.  Masks are left
   unchanged here; mask resets belong to the instruction-level consumer. *)
Theorem ld_take_adopt_shared_state:
  ld_shared_state tn un s t /\
  rq.cr_kind = rt.cr_kind /\ rq.cr_value = rt.cr_value /\
  rq.cr_target = rt.cr_target /\ rq.cr_data = rt.cr_data /\
  rq.cr_static = rt.cr_static /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient /\
  rt.cr_accounts = t.vs_accounts /\ rt.cr_tStorage = t.vs_transient ==>
  ld_shared_state tn un
    (s with <|
      vs_accounts := FST (adopt_outcome rq (FST (take_outcome rq s.vs_outcomes))
        (s.vs_accounts,s.vs_transient,s.vs_logs));
      vs_transient := FST (SND (adopt_outcome rq (FST (take_outcome rq s.vs_outcomes))
        (s.vs_accounts,s.vs_transient,s.vs_logs)));
      vs_outcomes := SND (take_outcome rq s.vs_outcomes);
      vs_returndata := (FST (take_outcome rq s.vs_outcomes)).co_returnData |>)
    (t with <|
      vs_accounts := FST (adopt_outcome rt (FST (take_outcome rt t.vs_outcomes))
        (t.vs_accounts,t.vs_transient,t.vs_logs));
      vs_transient := FST (SND (adopt_outcome rt (FST (take_outcome rt t.vs_outcomes))
        (t.vs_accounts,t.vs_transient,t.vs_logs)));
      vs_outcomes := SND (take_outcome rt t.vs_outcomes);
      vs_returndata := (FST (take_outcome rt t.vs_outcomes)).co_returnData |>)
Proof
  strip_tac >>
  drule_all ld_computed_precompile_cong >> strip_tac >>
  drule ld_shared_state_environment >> strip_tac >>
  Cases_on `t.vs_outcomes`
  >- (gvs[take_outcome_def, failed_outcome_def, adopt_outcome_def,
          ld_shared_state_def] >> IF_CASES_TAC >> gvs[]) >>
  Cases_on `computed_precompile rt`
  >- (gvs[take_outcome_def] >>
      Cases_on `precompile_result rt.cr_target rt.cr_data`
      >- gvs[failed_outcome_def, adopt_outcome_def, ld_shared_state_def] >>
      rename1 `_ = SOME v` >> Cases_on `v`
      >- gvs[failed_outcome_def, adopt_outcome_def, ld_shared_state_def] >>
      Cases_on `h.co_success` >>
      gvs[failed_outcome_def, adopt_outcome_def, ld_shared_state_def]) >>
  gvs[take_outcome_def, adopt_outcome_def] >>
  IF_CASES_TAC >>
  gvs[ld_shared_state_def, storage_agree_except_def, word_agree_except_def]
QED
