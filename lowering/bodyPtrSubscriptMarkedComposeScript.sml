Theory bodyPtrSubscriptMarkedCompose
Ancestors
  gasSummaryComposePtr fragGasPathPtr gasExemptCert gasOutcome
  gasSummary gasSummaryCompose exprSimDefs vyperState list

(* The callback sees the actual marked run, not an invented evaluation
   equation at an initial state whose gas observations have been erased. *)
Theorem array_index_outcome_compose_ptr:
  gas_marked_exec_ptr D (ctx,func) PG
    (a : evaluation_state -> eval_result evaluation_result)
    (es,s0,G0,tn0) left (INL captured) mid G1 tn1 (OK t) /\
  gas_outcome_ptr D tops (ctx,func) PG
    (b : evaluation_state -> value evaluation_result)
    (mid with gas_obs := [],t,G1,tn1)
    (\res ee G tn u. ?v. res = INL v /\ V v ee G tn u)
    (\res ee gt out. ?exc. res = INR exc /\ R (INR exc) ee gt out) /\
  (!imarks raw v Gi tni u.
     gas_marked_exec_ptr D (ctx,func) PG b
       (mid with gas_obs := [],t,G1,tn1) imarks (INL v) raw Gi tni (OK u) /\
     V v (raw with gas_obs := []) Gi tni u ==>
     gas_summary_ptr_at D (ctx,func) PG [] (k captured v)
       (raw with gas_obs := [],u,Gi,tni) Q R) ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (bind a (\r. bind b (k r))) (es,s0,G0,tn0) Q R
Proof
  strip_tac >> fs[gas_outcome_ptr_def] >>
  qexists_tac `left ++ marks`
  >- (qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_ONCE_REWRITE_RULE [gas_summary_ptr_at_marked])
      >- suspend "normal"
      >> suspend "exit") >> suspend "exempt"
QED

Resume array_index_outcome_compose_ptr[normal]:
  gvs[] >> disj1_tac >>
  irule gas_summary_ptr_at_bind_normal >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  irule (gas_summary_ptr_at_bind_normal |> Q.INST [`right` |-> `[]`]
    |> REWRITE_RULE [APPEND_NIL]) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Resume array_index_outcome_compose_ptr[exit]:
  gvs[] >> disj1_tac >>
  irule gas_summary_ptr_at_bind_normal >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  irule gas_summary_ptr_at_bind_exception >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume array_index_outcome_compose_ptr[exempt]:
  disj2_tac >> qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_result >>
  `gas_marked_exec F (ctx,func) a (es,s0) left (INL captured) mid (OK t)` by
    (irule gas_marked_exec_ptr_exec >> goal_assum (drule_at Any)) >>
  goal_assum (drule_at Any) >> BETA_TAC >> pure_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> first_assum ACCEPT_TAC
QED
Finalise array_index_outcome_compose_ptr

(* Match the whole normal post before inspecting its value tag. *)
Theorem array_index_outcome_post_compose_ptr:
  gas_outcome_ptr D tops (ctx,func) PG
    (b : evaluation_state -> value evaluation_result)
    (mid with gas_obs := [],t,G1,tn1) Qidx
    (\res ee gt out. ?exc. res = INR exc /\ R (INR exc) ee gt out) ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (a : evaluation_state -> eval_result evaluation_result)
    (es,s0,G0,tn0) left (INL captured) mid G1 tn1 (OK t) /\
  (!res ee Gi tni u. Qidx res ee Gi tni u ==> ?v. res = INL v) /\
  (!imarks raw v Gi tni u.
     gas_marked_exec_ptr D (ctx,func) PG b
       (mid with gas_obs := [],t,G1,tn1) imarks (INL v) raw Gi tni (OK u) /\
     Qidx (INL v) (raw with gas_obs := []) Gi tni u ==>
     gas_summary_ptr_at D (ctx,func) PG [] (k captured v)
       (raw with gas_obs := [],u,Gi,tni) Q R) ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (bind a (\r. bind b (k r))) (es,s0,G0,tn0) Q R
Proof
  rpt strip_tac >>
  irule array_index_outcome_compose_ptr >>
  qexistsl_tac [`G1`, `\v ee Gi tni u. Qidx (INL v) ee Gi tni u`,
    `captured`, `left`, `mid`, `t`, `tn1`] >>
  simp[] >> conj_tac >- metis_tac[] >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED
