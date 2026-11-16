Theory assignPlaceEmptySource
Ancestors
  assignPlaceEmpty aggregateCountedOutcome gasSummaryCompose gasExemptCert
  fragGasMode fragGasPath immutableAssignEmpty gasSummary gasOutcome
  vyperInterpreter vyperState

Theorem assign_place_empty_prefix_outcome:
  expr_body_pre cenv cx env e es /\ is_empty_value_expr e /\
  has_length_word (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ ~s0.vs_halted /\
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (eval_target_place cx bt) (\p. write_place cx p (default_value dtv)))
    (es with gas_obs := [],s0) Q R ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (eval_stmt cx (Assign (BaseTarget bt) e)) (es,s0) Q R
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,func)
     (bind (eval_expr cx e) (read_result cx)) (es,s0)
     [] (INL (default_value dtv)) es (OK s0)` by
    (drule_all immutable_assign_empty_read >> strip_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules] >>
     metis_tac[gas_marked_exec_def, gas_marked_path_def,
       gas_path_rules, immutable_assign_empty_read]) >>
  `eval_stmt cx (Assign (BaseTarget bt) e) =
     bind (bind (eval_expr cx e) (read_result cx))
       (\v. bind (eval_target_place cx bt) (\p. write_place cx p v))` by
    simp[Once evaluate_def, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  irule counted_outcome_prefix >> goal_assum (drule_at Any) >>
  reverse conj_tac >- (BETA_TAC >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
  once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  goal_assum (drule_at Any) >> fs[GSYM ignore_bind_def]
QED
