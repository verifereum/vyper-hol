(* Counted sequencing, including exemptions in either operand. *)
Theory exprSimExtract32Counted
Ancestors
  gasOutcome gasSummary gasExemptCert gasSummaryCompose gasStorage vyperState
  vyperStorageTrace vyperStorageFootprint stmtSimDeclCompose

(* The continuation receives the operand's post at every valid horizon of
   its end trace, together with one such horizon. *)
Theorem extract32_outcome_bind_marked:
  gas_outcome memory tops (ctx,func) cx st0
    (a : evaluation_state -> value evaluation_result) (es,s0)
    (\H res ee t. ?v. res = INL v /\ P H v ee t)
    (\H res ee r. ?exc. res = INR exc /\ R H (INR exc) ee r) /\
  (!marks v ee t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks (INL v) ee (OK t) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> P H v ee t) /\
    (?H. valid_horizon cx st0 H ee.storage_trace) /\ ee.gas_obs = [] ==>
    gas_outcome memory tops (ctx,func) cx st0 (k v) (ee,t) Q R) /\
  (!v. storage_trace_frame (k v)) ==>
  gas_outcome memory tops (ctx,func) cx st0 (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ a _ _ _`
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
          `gas_marked_exec memory (ctx,func) a (es,s0) marks (INL v)
             (mid with gas_obs := []) (OK t)` by
            metis_tac[gas_marked_exec_end_gas_obs] >>
          `gas_outcome memory tops (ctx,func) cx st0 (k v)
             (mid with gas_obs := [],t) Q R` by
            (first_x_assum irule >> simp[] >> rpt conj_tac >>
             TRY (metis_tac[] >> NO_TAC) >> rpt strip_tac >>
             `?v'. INL v = INL v' /\ P H v' (mid with gas_obs := []) t` by
               metis_tac[] >> gvs[]) >>
          pop_assum (mp_tac o REWRITE_RULE [gas_outcome_def]) >>
          disch_then (qx_choose_then `right` (DISJ_CASES_THEN mp_tac))
          >- (strip_tac >> rewrite_tac[gas_outcome_def] >>
              qexists_tac `marks ++ right` >> disj1_tac >>
              irule gas_bad_storage_at_bind_right >> metis_tac[]) >>
          disch_then (DISJ_CASES_THEN mp_tac)
          >- (rewrite_tac[gas_summary_at_def] >>
              disch_then (qx_choose_then `out` (qx_choose_then `fin`
                (qx_choose_then `r'` (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
              rewrite_tac[gas_outcome_def] >>
              qexists_tac `marks ++ right` >> disj2_tac >> disj1_tac >>
              rewrite_tac[gas_summary_at_def] >>
              qexistsl_tac [`out`, `fin`, `r'`] >>
              conj_tac >- (irule gas_marked_exec_bind_normal >>
                            goal_assum drule >> simp[]) >>
              first_assum ACCEPT_TAC) >>
          strip_tac >>
          rewrite_tac[gas_outcome_def] >>
          qexists_tac `marks ++ right` >> disj2_tac >> disj2_tac >>
          rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
          irule_at Any gas_exempt_cert_bind_value >>
          simp[GSYM ignore_bind_def] >> metis_tac[]) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      `?ex. res = INR ex` by metis_tac[] >> gvs[] >>
      rewrite_tac[gas_outcome_def] >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR ex`, `mid`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      BETA_TAC >> simp[] >> rpt strip_tac >>
      `?ex'. INR ex = INR ex' /\ R H (INR ex') (mid with gas_obs := []) r` by
        metis_tac[] >>
      gvs[]) >>
  strip_tac >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule_at Any gas_exempt_cert_error_value >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Theorem extract32_outcome_bind_value:
  gas_outcome memory tops (ctx, func) cx st0
    (a : evaluation_state -> value evaluation_result) (es, s0)
    (\H res mid t. ?v. res = INL v /\
       gas_outcome memory tops (ctx, func) cx st0 (k v) (mid, t) Q R)
    (\H res ee r. ?exc. res = INR exc /\ R H (INR exc) ee r) /\
  (!v. storage_trace_frame (k v)) ==>
  gas_outcome memory tops (ctx, func) cx st0 (bind a k) (es, s0) Q R
Proof
  strip_tac >> irule extract32_outcome_bind_marked >> simp[] >>
  qexists_tac `\H v mid t.
    gas_outcome memory tops (ctx, func) cx st0 (k v) (mid, t) Q R` >>
  simp[] >> metis_tac[]
QED

(* The preparation is an actual marked execution; it is not inferred from
   an uncounted fragment. The continuation can itself exempt. *)
Theorem extract32_outcome_read_prefix:
  gas_marked_exec memory (ctx, func)
    (a : evaluation_state -> value evaluation_result)
    (es, s0) [] (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx, func) cx st0 (k v)
    (mid with gas_obs := [], t) Q R ==>
  gas_outcome memory tops (ctx, func) cx st0 (bind a k) (es, s0) Q R
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `right` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> qexists_tac `[] ++ right` >> disj1_tac >>
      irule gas_bad_storage_at_bind_right >> metis_tac[]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `out` (qx_choose_then `fin`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
      qexists_tac `[] ++ right` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`out`, `fin`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_normal >>
                    goal_assum drule >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  qexists_tac `[] ++ right` >> disj2_tac >> disj2_tac >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule_at Any gas_exempt_cert_bind_value >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Theorem extract32_outcome_return_prefix:
  gas_marked_exec memory (ctx,func) (return (v:value)) (es,s0) []
    (INL v) es (OK t) /\ es.gas_obs = [] /\
  gas_outcome memory tops (ctx,func) cx st0
    (b : evaluation_state -> eval_result evaluation_result) (es,t) Q R ==>
  gas_outcome memory tops (ctx,func) cx st0 b (es,s0) Q R
Proof
  strip_tac >>
  `es with gas_obs := [] = es` by simp[evaluation_state_component_equality] >>
  qspecl_then [`return v`, `\x:value. b`] mp_tac
    (Q.GENL [`a`,`k`] (Q.INST [`mid` |-> `es`]
       (SPEC_ALL extract32_outcome_read_prefix))) >>
  simp[vyperStateTheory.bind_return] >>
  disch_then irule >> simp[]
QED
