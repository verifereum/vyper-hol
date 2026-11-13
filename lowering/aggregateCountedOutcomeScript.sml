(* Small polymorphic outcome adapters for counted aggregate evaluation. *)
Theory aggregateCountedOutcome
Ancestors
  gasOutcome gasSummary gasSummaryCompose gasExemptCert fragGasMode fragGasPath
  vyperState venomState list fragGasPathMem
  gasStorage vyperStorageTrace vyperStorageFootprint
Libs
  monadsyntax

Theorem counted_outcome_return:
  ~s.vs_halted /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     Q H (INL v) (es with gas_obs := []) s) ==>
  gas_outcome memory tops (ctx,func) cx st0 (return v) (es,s) Q R
Proof
  strip_tac >> simp[gas_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INL v`, `es`, `OK s`] >>
  simp[gas_marked_exec_def, return_def] >>
  Cases_on `memory` >> simp[gas_marked_path_def] >>
  metis_tac[gas_path_rules, gas_path_mem_rules]
QED

Theorem counted_outcome_conseq:
  gas_outcome memory tops p cx st0 source start Q R /\
  (!H res ee t. Q H res ee t ==> Q' H res ee t) /\
  (!H res ee r. R H res ee r ==> R' H res ee r) ==>
  gas_outcome memory tops p cx st0 source start Q' R'
Proof
  Cases_on `p` >> Cases_on `start` >>
  simp[gas_outcome_def, gas_summary_at_def] >> metis_tac[]
QED

Theorem counted_outcome_prefix:
  gas_marked_exec memory (ctx,func) a (es,s0) left (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx,func) cx st0 (k v) (mid with gas_obs := [],t) Q R /\
  (!right err ee leaf finish.
    gas_exempt_cert memory tops (ctx,func) (ignore_bind (k v) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,finish) ==>
    gas_exempt_cert memory tops (ctx,func) (ignore_bind (bind a k) (return ()))
      (es,s0) (left ++ right) (err,ee) (leaf,finish)) ==>
  gas_outcome memory tops (ctx,func) cx st0 (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `right` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> qexists_tac `left ++ right` >> disj1_tac >>
      irule gas_bad_storage_at_bind_right >>
      metis_tac[]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `fin`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
      qexists_tac `left ++ right` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`res`, `fin`, `r`] >>
      conj_tac
      >- (irule gas_marked_exec_bind_normal >>
          goal_assum (drule_at Any) >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >> qexists_tac `left ++ right` >> disj2_tac >> disj2_tac >>
  metis_tac[]
QED

Theorem counted_outcome_bind_exec:
  gas_outcome memory tops (ctx,func) cx st0 a (es,s0) P Exit /\
  (!H res ee t. P H res ee t ==> ?v. res = INL v) /\
  (!H res ee r. Exit H res ee r ==> ?ex. res = INR ex /\ R H (INR ex) ee r) /\
  (!marks v mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks (INL v) mid (OK t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       P H (INL v) (mid with gas_obs := []) t) ==>
    gas_outcome memory tops (ctx,func) cx st0 (k v) (mid with gas_obs := [],t) Q R) /\
  (!left v mid t right err ee leaf finish.
    gas_marked_exec memory (ctx,func) a (es,s0) left (INL v) mid (OK t) /\
    gas_exempt_cert memory tops (ctx,func) (ignore_bind (k v) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,finish) ==>
    gas_exempt_cert memory tops (ctx,func) (ignore_bind (bind a k) (return ()))
      (es,s0) (left ++ right) (err,ee) (leaf,finish)) /\
  (!marks err ee leaf finish.
    gas_exempt_cert memory tops (ctx,func) (ignore_bind a (return ()))
      (es,s0) marks (err,ee) (leaf,finish) ==>
    gas_exempt_cert memory tops (ctx,func) (ignore_bind (bind a k) (return ()))
      (es,s0) marks (err,ee) (leaf,finish)) /\
  (!v. storage_trace_frame (k v)) ==>
  gas_outcome memory tops (ctx,func) cx st0 (bind a k) (es,s0) Q R
Proof
  strip_tac >> qpat_x_assum `gas_outcome _ _ _ _ _ a _ _ _`
    (mp_tac o BETA_RULE o REWRITE_RULE [gas_outcome_def]) >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> rewrite_tac[gas_outcome_def] >>
      qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >> simp[]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >> BETA_TAC >>
      disch_then (qx_choose_then `res` (qx_choose_then `mid`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      reverse (Cases_on `storage_trace_domain cx st0 mid.storage_trace`)
      >- (disch_then kall_tac >> rewrite_tac[gas_outcome_def] >>
          qexists_tac `marks` >> disj1_tac >>
          irule gas_bad_storage_at_bind_left >> simp[] >>
          irule gas_bad_storage_at_counted_prefix >>
          metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by fs[storage_trace_domain_def] >>
      disch_then (DISJ_CASES_THEN strip_assume_tac)
      >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
            (assume_tac o SIMP_RULE (srw_ss()) []) >>
          `?v. res = INL v` by metis_tac[] >> gvs[] >>
          irule counted_outcome_prefix >>
          goal_assum (drule_at Any) >> conj_tac >- metis_tac[] >>
          first_x_assum irule >> simp[] >> goal_assum (drule_at Any)) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      `?ex. res = INR ex` by metis_tac[] >> gvs[] >>
      rewrite_tac[gas_outcome_def] >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR ex`, `mid`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      BETA_TAC >> simp[] >> disj2_tac >> rpt strip_tac >>
      `?ex'. INR ex = INR ex' /\ R H (INR ex') (mid with gas_obs := []) r` by
        metis_tac[] >>
      gvs[]) >>
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem counted_outcome_map_values:
  gas_outcome memory tops (ctx,func) cx st0
    (a : evaluation_state -> (value list) evaluation_result) (es,s0)
    (\H res ee t. ?vs. res = INL vs /\ P H vs ee t)
    (\H res ee r. ?ex. res = INR ex /\ R H (INR ex) ee r) /\
  (!H vs ee t. P H vs ee t ==> ~t.vs_halted) ==>
  gas_outcome memory tops (ctx,func) cx st0 (bind a (\vs. return (f vs))) (es,s0)
    (\H res ee t. ?vs. res = INL (f vs) /\ P H vs ee t) R
Proof
  strip_tac >> irule counted_outcome_bind_exec >>
  conj_tac >- simp[storage_trace_frame_return] >> conj_tac
  >- (rpt strip_tac >>
      pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_values >> goal_assum (drule_at Any) >>
      gvs[GSYM ignore_bind_def]) >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_values >> simp[]) >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      reverse (Cases_on `storage_trace_domain cx st0 mid.storage_trace`)
      >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
          simp[gas_bad_storage_at_def, return_def]) >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by fs[storage_trace_domain_def] >>
      irule counted_outcome_return >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED
