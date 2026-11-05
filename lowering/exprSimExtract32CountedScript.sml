(* Counted sequencing, including exemptions in either operand. *)
Theory exprSimExtract32Counted
Ancestors
  gasOutcome gasSummary gasExemptCert gasSummaryCompose vyperState
  stmtSimDeclCompose

Theorem extract32_outcome_bind_value:
  gas_outcome memory tops (ctx, func)
    (a : evaluation_state -> value evaluation_result) (es, s0)
    (\res mid t. ?v. res = INL v /\
       gas_outcome memory tops (ctx, func) (k v) (mid, t) Q R)
    (\res ee r. ?exc. res = INR exc /\ R (INR exc) ee r) ==>
  gas_outcome memory tops (ctx, func) (bind a k) (es, s0) Q R
Proof
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      gvs[]
      >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
          rewrite_tac[gas_summary_at_def] >>
          qexistsl_tac [`res'`, `es_end'`, `OK t'`] >> simp[] >>
          irule gas_marked_exec_bind_normal >>
          goal_assum (drule_at Any) >> simp[])
      >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
          rewrite_tac[gas_summary_at_def] >>
          qexistsl_tac [`res'`, `es_end'`, `r`] >> simp[] >>
          irule gas_marked_exec_bind_normal >>
          goal_assum (drule_at Any) >> simp[])
      >- (qexists_tac `marks ++ marks'` >> disj2_tac >>
          rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
          irule_at Any gas_exempt_cert_bind_value >>
          goal_assum (drule_at Any) >> simp[GSYM ignore_bind_def] >>
          metis_tac[]) >>
      qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      irule_at Any gas_marked_exec_bind_exception >>
      goal_assum (drule_at Any) >> simp[])
  >> qexists_tac `marks` >> disj2_tac >>
     rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
     irule_at Any gas_exempt_cert_error_value >>
     simp[GSYM ignore_bind_def] >> metis_tac[]
QED

(* The preparation is an actual marked execution; it is not inferred from
   an uncounted fragment. The continuation can itself exempt. *)
Theorem extract32_outcome_read_prefix:
  gas_marked_exec memory (ctx, func)
    (a : evaluation_state -> value evaluation_result)
    (es, s0) [] (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx, func) (k v)
    (mid with gas_obs := [], t) Q R ==>
  gas_outcome memory tops (ctx, func) (bind a k) (es, s0) Q R
Proof
  strip_tac >> irule extract32_outcome_bind_value >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL v`, `mid`, `OK t`] >> simp[] >>
  fs[gas_outcome_def, gas_summary_at_def] >> metis_tac[]
QED

Theorem extract32_outcome_bind_marked:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> value evaluation_result) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. ?exc. res = INR exc /\ R (INR exc) ee r) /\
  (!marks v ee t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks (INL v) ee (OK t) /\
    P v ee t /\ ee.gas_obs = [] ==>
    gas_outcome memory tops (ctx,func) (k v) (ee,t) Q R) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >> irule extract32_outcome_bind_value >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (gvs[] >>
      `gas_marked_exec memory (ctx,func) a (es,s0) marks (INL v)
         (es_end with gas_obs := []) (OK t)` by
        metis_tac[gas_marked_exec_end_gas_obs] >>
      `gas_outcome memory tops (ctx,func) (k v)
         (es_end with gas_obs := [],t) Q R` by
        (first_x_assum irule >> simp[] >> qexists_tac `marks` >> simp[]) >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INL v`, `es_end`, `OK t`] >>
      gvs[gas_outcome_def, gas_summary_at_def] >> metis_tac[])
  >- (qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Theorem extract32_outcome_return_prefix:
  gas_marked_exec memory (ctx,func) (return (v:value)) (es,s0) []
    (INL v) es (OK t) /\ es.gas_obs = [] /\
  gas_outcome memory tops (ctx,func)
    (b : evaluation_state -> eval_result evaluation_result) (es,t) Q R ==>
  gas_outcome memory tops (ctx,func) b (es,s0) Q R
Proof
  strip_tac >>
  `es with gas_obs := [] = es` by simp[evaluation_state_component_equality] >>
  qspecl_then [`return v`, `\x:value. b`] mp_tac
    (Q.GENL [`a`,`k`] (Q.INST [`mid` |-> `es`]
       (SPEC_ALL extract32_outcome_read_prefix))) >>
  simp[vyperStateTheory.bind_return] >>
  disch_then irule >> simp[]
QED
