(* Reachability interface for the conditional aggregate children predicate. *)
Theory bodyMemAggregateLoopBoundary
Ancestors
  bodyMemoryPreds gasSummary gasOutcome gasSummaryCompose gasExemptCert vyperState

Theorem aggregate_body_exprs_mem_tail:
  body_exprs_mem_ok cx (e::args) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s)
    marks (INL tv) ee (OK r) /\
  gas_marked_exec T (ctx,func) (read_result cx tv) (ee,r)
    [] (INL v) ee' (OK q) ==>
  body_exprs_mem_ok cx args
Proof
  simp[body_exprs_mem_ok_def, gas_marked_exec_def] >>
  rpt strip_tac >>
  first_x_assum irule >>
  metis_tac[]
QED

Theorem aggregate_tuple_bind_outcome_any:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. ?exc. res = INR exc /\ R (INR exc) ee r) /\
  (!marks v ee t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks (INL v) ee (OK t) /\
    ee.gas_obs = [] /\ P v ee t ==>
    gas_outcome memory tops (ctx,func)
      (k v : evaluation_state -> value list evaluation_result) (ee,t) Q R) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (gvs[] >>
      first_x_assum (qspecl_then [`left`, `v`, `es_end with gas_obs := []`, `t`] mp_tac) >>
      (impl_tac >- fs[gas_marked_exec_def]) >>
      rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
      disch_then (qx_choose_then `right` strip_assume_tac)
      >- (qexists_tac `left ++ right` >> disj1_tac >>
          metis_tac[gas_marked_exec_bind_normal])
      >- (qexists_tac `left ++ right` >> disj1_tac >>
          metis_tac[gas_marked_exec_bind_normal]) >>
      qexists_tac `left ++ right` >> disj2_tac >>
      rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
      irule_at Any gasExemptCertTheory.gas_exempt_cert_bind_result >>
      simp[GSYM ignore_bind_def] >> metis_tac[])
  >- (gvs[] >> qexists_tac `left` >> disj1_tac >>
      metis_tac[gas_marked_exec_bind_exception]) >>
  qexists_tac `left` >> disj2_tac >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule_at Any gasExemptCertTheory.gas_exempt_cert_error_result >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Theorem aggregate_tuple_value_bind_any:
  gas_marked_exec memory (ctx,func)
    (a : evaluation_state -> value evaluation_result) (es,s0)
    left (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx,func)
    (k v : evaluation_state -> value list evaluation_result)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `right` strip_assume_tac))
  >- (qexists_tac `left ++ right` >> disj1_tac >>
      metis_tac[gas_marked_exec_bind_normal])
  >- (qexists_tac `left ++ right` >> disj1_tac >>
      metis_tac[gas_marked_exec_bind_normal]) >>
  qexists_tac `left ++ right` >> disj2_tac >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule_at Any gasExemptCertTheory.gas_exempt_cert_bind_value >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Theorem aggregate_tuple_ignore_values_mem[local]:
  ignore_bind (bind (eval_exprs cx args) (\vs. return (v::vs))) (return ()) =
  ignore_bind (eval_exprs cx args) (return ())
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def] >> gen_tac >>
  Cases_on `eval_exprs cx args x` >> Cases_on `q` >> simp[]
QED

Theorem aggregate_tuple_values_outcome_any:
  gas_outcome memory tops (ctx,func) (eval_exprs cx args) (es,s) Q1 R1 /\
  (!res ee r. Q1 res ee r ==>
     Q (case res of INL vs => INL (v::vs) | INR exc => INR exc) ee r) /\
  (!res ee r. R1 res ee r ==>
     R (case res of INL vs => INL (v::vs) | INR exc => INR exc) ee r) ==>
  gas_outcome memory tops (ctx,func)
    (bind (eval_exprs cx args) (\vs. return (v::vs))) (es,s) Q R
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def,
              aggregate_tuple_ignore_values_mem] >>
  strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      qexistsl_tac [`case res of INL vs => INL (v::vs) | INR exc => INR exc`,
                    `es_end`, `OK t`] >>
      qpat_x_assum `!res ee r. Q1 _ _ _ ==> _` drule >>
      Cases_on `res` >> fs[gas_marked_exec_def, bind_def, return_def])
  >- (disj1_tac >>
      qexistsl_tac [`case res of INL vs => INL (v::vs) | INR exc => INR exc`,
                    `es_end`, `r`] >>
      qpat_x_assum `!res ee r. R1 _ _ _ ==> _` drule >>
      Cases_on `res` >> fs[gas_marked_exec_def, bind_def, return_def]) >>
  disj2_tac >> metis_tac[]
QED
