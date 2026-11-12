Theory lowerDloadOracleSelection
Ancestors
  extCallOracle list

Theorem ld_computed_precompile_cong:
  rq.cr_kind = rq'.cr_kind /\ rq.cr_value = rq'.cr_value /\
  rq.cr_target = rq'.cr_target /\ rq.cr_data = rq'.cr_data ==>
  (computed_precompile rq <=> computed_precompile rq')
Proof
  simp[computed_precompile_def]
QED

(* Remaining-stream equality is already take_outcome_rest; no duplicate. *)

Theorem ld_take_outcome_success_cong:
  rq.cr_kind = rq'.cr_kind /\ rq.cr_value = rq'.cr_value /\
  rq.cr_target = rq'.cr_target /\ rq.cr_data = rq'.cr_data ==>
  (FST (take_outcome rq os)).co_success =
  (FST (take_outcome rq' os)).co_success
Proof
  strip_tac >> drule_all ld_computed_precompile_cong >> strip_tac >>
  Cases_on `os` >> simp[take_outcome_def, failed_outcome_def] >>
  Cases_on `computed_precompile rq'` >> gvs[] >>
  Cases_on `precompile_result rq'.cr_target rq'.cr_data` >> simp[] >>
  rename1 `SOME v` >> Cases_on `v` >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem ld_take_outcome_returndata_cong:
  rq.cr_kind = rq'.cr_kind /\ rq.cr_value = rq'.cr_value /\
  rq.cr_target = rq'.cr_target /\ rq.cr_data = rq'.cr_data ==>
  (FST (take_outcome rq os)).co_returnData =
  (FST (take_outcome rq' os)).co_returnData
Proof
  strip_tac >> drule_all ld_computed_precompile_cong >> strip_tac >>
  Cases_on `os` >> simp[take_outcome_def, failed_outcome_def] >>
  Cases_on `computed_precompile rq'` >> gvs[] >>
  Cases_on `precompile_result rq'.cr_target rq'.cr_data` >> simp[] >>
  rename1 `SOME v` >> Cases_on `v` >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem ld_take_outcome_created_cong:
  rq.cr_kind = rq'.cr_kind /\ rq.cr_value = rq'.cr_value /\
  rq.cr_target = rq'.cr_target /\ rq.cr_data = rq'.cr_data ==>
  (FST (take_outcome rq os)).co_created =
  (FST (take_outcome rq' os)).co_created
Proof
  strip_tac >> drule_all ld_computed_precompile_cong >> strip_tac >>
  Cases_on `os` >> simp[take_outcome_def, failed_outcome_def] >>
  Cases_on `computed_precompile rq'` >> gvs[] >>
  Cases_on `precompile_result rq'.cr_target rq'.cr_data` >> simp[] >>
  rename1 `SOME v` >> Cases_on `v` >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem ld_record_request_growth:
  (record_request rq rqs <> rqs) <=> ~computed_precompile rq
Proof
  Cases_on `computed_precompile rq` >> simp[record_request_def] >>
  strip_tac >> first_x_assum (mp_tac o AP_TERM ``LENGTH``) >> simp[]
QED

Theorem ld_record_request_growth_cong:
  rq.cr_kind = rq'.cr_kind /\ rq.cr_value = rq'.cr_value /\
  rq.cr_target = rq'.cr_target /\ rq.cr_data = rq'.cr_data ==>
  ((record_request rq rqs <> rqs) <=> (record_request rq' rqs' <> rqs'))
Proof
  strip_tac >> drule_all ld_computed_precompile_cong >>
  metis_tac[ld_record_request_growth]
QED
