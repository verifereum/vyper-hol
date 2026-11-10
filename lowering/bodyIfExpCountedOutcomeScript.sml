(* Conditional-result outcomes with an arbitrary counted marked continuation. *)
Theory bodyIfExpCountedOutcome
Ancestors
  exprSimSubscriptMap gasOutcome gasSummary exprSimDefs

Theorem ifexp_raw_counted_conditional_outcome_mem:
  gas_outcome T tops (ctx,func) (eval_expr cx e) (es,s0) P
    (\res ee r. expr_exit res r) /\
  (!res ee s. P res ee s ==> ?raw. res = INL raw) /\
  (!marks raw ee s.
    gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
      marks (INL raw) ee (OK s) /\ P (INL raw) (ee with gas_obs := []) s ==>
    ?right tv q. gas_marked_exec T (ctx,func) (conditional_result cx raw)
      (ee with gas_obs := [],s) right (INL tv) (ee with gas_obs := []) (OK q) /\
      Q (INL tv) (ee with gas_obs := []) q) ==>
  gas_outcome T tops (ctx,func)
    (bind (eval_expr cx e) (conditional_result cx)) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (Cases >> simp[expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!marks raw ee s. _` drule_all >> strip_tac >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  qexists_tac `right` >> disj1_tac >>
  qexistsl_tac [`INL tv`,`mid with gas_obs := []`,`OK q`] >> simp[]
QED
