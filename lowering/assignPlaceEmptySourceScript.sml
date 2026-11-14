Theory assignPlaceEmptySource
Ancestors
  assignPlaceEmpty assignPlaceGasCompose gasSummaryCompose gasExemptCert
  fragGasMode fragGasPath immutableAssignEmpty gasSummary gasOutcome
  vyperInterpreter vyperState

Theorem assign_place_empty_prefix_outcome:
  expr_body_pre cenv cx env e es /\ is_empty_value_expr e /\
  has_length_word (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ ~s0.vs_halted /\
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_target_place cx bt) (\p. write_place cx p (default_value dtv)))
    (es with gas_obs := [],s0) Q R ==>
  gas_outcome F (cx_tops cx) (ctx,func)
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
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >>
      (conj_tac
       >- (simp[Once evaluate_def, GSYM bind_assoc] >>
           irule (SRULE [] (Q.INST [`left` |-> `[]`]
             (SPEC_ALL gas_marked_exec_bind_normal))) >>
           metis_tac[])) >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`]
    (SPEC_ALL gas_exempt_cert_bind_value))) >>
  goal_assum (drule_at Any) >> gvs[ignore_bind_def, bind_assoc]
QED
