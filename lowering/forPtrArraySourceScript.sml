(* No-code iterator prefix for the public array fragment. *)
Theory forPtrArraySource
Ancestors gasSummaryComposePtr gasOutcomeInitialObsPtr fragGasPathPtr
  gasExemptCert gasNormalPrefix gasSummary gasContext loweringPosts
  vyperInterpreter vyperState vyperValue
Libs monadsyntax

Theorem for_values_prefix_outcome_ptr:
  (!gs. source (es with gas_obs := gs) = (INL (vs:value list), es with gas_obs := gs)) /\
  ~s.vs_halted /\
  gas_outcome_ptr D tops (ctx,func) PG (next vs) (es with gas_obs := [],s,G,tn) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG (bind source next) (es,s,G,tn) Q R
Proof
  strip_tac >>
  `gas_marked_exec_ptr D (ctx,func) PG source (es,s,G,tn) []
    (INL vs) es G tn (OK s)` by
    (simp[gas_marked_exec_ptr_def, gas_explicit_def] >>
     irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  irule gas_outcome_ptr_bind_normal >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[ignore_bind_def, bind_assoc] >>
  drule gas_exempt_cert_bind_values >>
  disch_then (qspecl_then [`tops`, `\v. bind (next v) (\x. return ())`] mp_tac) >>
  fs[ignore_bind_def] >> disch_then drule >> simp[]
QED

Theorem for_array_source_prefix_ptr:
  (!gs. eval_iterator cx (Array (Name (ArrayT et (Fixed n)) name))
    (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) /\
  LENGTH vs = n /\ evaluate_type (get_tenv cx) et = SOME tv /\ ~s.vs_halted /\
  gas_outcome_ptr D tops (ctx,func) PG (eval_for cx tv id stmts vs)
    (es with gas_obs := [],s,G,tn) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (eval_stmt cx (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts))
    (es,s,G,tn) Q R
Proof
  strip_tac >>
  `!msg. assert T msg = return ()` by
    simp[FUN_EQ_THM, vyperStateTheory.assert_def, return_def] >>
  simp[Once evaluate_def, lift_option_type_def, lift_option_def, bind_return] >>
  irule for_values_prefix_outcome_ptr >> simp[] >>
  simp[compatible_bound_def, check_def, vyperStateTheory.assert_def,
    ignore_bind_def, bind_return]
QED

Theorem for_array_source_admissible:
  (!gs. eval_iterator cx (Array (Name (ArrayT et (Fixed n)) name))
    (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) /\
  LENGTH vs = n /\ evaluate_type (get_tenv cx) et = SOME tv /\
  gas_admissible
    (eval_stmt cx (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts))
    (stmt_res_ok lctx) es ==>
  gas_admissible (eval_for cx tv id stmts vs) (stmt_res_ok lctx) es
Proof
  simp[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs res es'. _` (qspec_then `gs` mp_tac) >>
  simp[Once evaluate_def, lift_option_type_def, lift_option_def, bind_return,
    bind_def, ignore_bind_def, compatible_bound_def, check_def,
    vyperStateTheory.assert_def, return_def]
QED
