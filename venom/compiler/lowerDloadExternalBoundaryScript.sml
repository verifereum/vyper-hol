(* External completion observations: no equality of masked requests is required. *)
Theory lowerDloadExternalBoundary
Ancestors
  lowerDloadSafetyKernel lowerDloadSafetyValues ptrDiscipline extCallOracle pair vfmState

Theorem ld_take_outcome_rest:
  rq.cr_target = rq'.cr_target /\ rq.cr_value = rq'.cr_value /\
  rq.cr_data = rq'.cr_data ==>
  SND (take_outcome rq os) = SND (take_outcome rq' os)
Proof
  strip_tac >> Cases_on `os` >>
  Cases_on `precompile_result rq'.cr_target rq'.cr_data` >>
  Cases_on `rq'.cr_value = 0` >>
  gvs[take_outcome_def, computed_precompile_def, failed_outcome_def] >>
  rename1 `precompile_result _ _ = SOME result` >>
  Cases_on `result` >> simp[failed_outcome_def]
QED

Theorem ld_take_outcome_success:
  rq.cr_target = rq'.cr_target /\ rq.cr_value = rq'.cr_value /\
  rq.cr_data = rq'.cr_data ==>
  (FST (take_outcome rq os)).co_success =
    (FST (take_outcome rq' os)).co_success
Proof
  strip_tac >> Cases_on `os` >>
  Cases_on `precompile_result rq'.cr_target rq'.cr_data` >>
  Cases_on `rq'.cr_value = 0` >>
  gvs[take_outcome_def, computed_precompile_def, failed_outcome_def] >>
  rename1 `precompile_result _ _ = SOME result` >>
  Cases_on `result` >> simp[failed_outcome_def]
QED

Theorem ld_take_outcome_returndata:
  rq.cr_target = rq'.cr_target /\ rq.cr_value = rq'.cr_value /\
  rq.cr_data = rq'.cr_data ==>
  (FST (take_outcome rq os)).co_returnData =
    (FST (take_outcome rq' os)).co_returnData
Proof
  strip_tac >> Cases_on `os` >>
  Cases_on `precompile_result rq'.cr_target rq'.cr_data` >>
  Cases_on `rq'.cr_value = 0` >>
  gvs[take_outcome_def, computed_precompile_def, failed_outcome_def] >>
  rename1 `precompile_result _ _ = SOME result` >>
  Cases_on `result` >> simp[failed_outcome_def]
QED

Theorem ld_nonghost_accounts_empty:
  ld_nonghost tn s t /\ tn.t_stor = {} ==>
  s.vs_accounts = t.vs_accounts
Proof
  strip_tac >> fs[ld_nonghost_def] >>
  simp[FUN_EQ_THM] >> gen_tac >>
  qpat_x_assum `!a. _ /\ _` (qspec_then `x` strip_assume_tac) >>
  `(s.vs_accounts x).storage = (t.vs_accounts x).storage` by
    fs[storage_agree_except_def, key_taint_def, ld_word_agree_empty,
       FUN_EQ_THM] >>
  qpat_x_assum `(s.vs_accounts x).storage = _`
    (fn th => fs[GSYM th])
QED

Theorem ld_nonghost_transient_empty:
  ld_nonghost tn s t /\ tn.t_trans = {} ==>
  s.vs_transient = t.vs_transient
Proof
  strip_tac >> fs[ld_nonghost_def] >>
  fs[storage_agree_except_def, key_taint_def, ld_word_agree_empty,
     FUN_EQ_THM]
QED
