Theory stmtForArrayMemorySupport
Ancestors
  stmtSimDefs stmtSimDeclGas exprSimWordArgs gasOutcome gasSummary gasContext gasExemptCert
  vyperState vyperInterpreter vyperValue vyperTypeSystem fragGasMode fragGasPathMem

Theorem gas_outcome_start_gas_obs:
  gas_outcome memory tops (ctx,func) source (es,s0) Q R ==>
  gas_outcome memory tops (ctx,func) source (es with gas_obs := gs,s0) Q R
Proof
  pure_rewrite_tac [gas_outcome_def] >> strip_tac >> qexists `marks`
  >- (disj1_tac >> qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_at_def, gas_marked_exec_def]) >>
  disj2_tac >> drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `gs` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem stmt_frag_mem_start_gas_obs:
  stmt_frag_mem d ctx func cx lc RetQ ce m source es ==>
  stmt_frag_mem d ctx func cx lc RetQ ce m source (es with gas_obs := gs)
Proof
  rw[stmt_frag_mem_def] >>
  irule gas_outcome_start_gas_obs >>
  first_x_assum irule >> simp[]
QED

Theorem array_for_source_prefix_mem:
  !tops ctx func cx id et it n body tv vs es s0 Q R.
  evaluate_type (get_tenv cx) et = SOME tv /\
  LENGTH vs = n /\ ~s0.vs_halted /\
  (!gs. eval_iterator cx it (es with gas_obs := gs) =
        (INL vs, es with gas_obs := gs)) /\
  gas_outcome T tops (ctx,func) (eval_for cx tv id body vs) (es,s0) Q R ==>
  gas_outcome T tops (ctx,func) (eval_stmt cx (For id et it n body)) (es,s0) Q R
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_at_def, gas_marked_exec_def, Once evaluate_def,
           bind_def, lift_option_type_def, ignore_bind_def, check_def,
           compatible_bound_def, vyperStateTheory.assert_def, return_def]) >>
  disj2_tac >>
  `assert T (Error (RuntimeError "For too long")) = return ()` by
    simp[FUN_EQ_THM, vyperStateTheory.assert_def, return_def] >>
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[Once evaluate_def, lift_option_type_def, bind_return,
       ignore_bind_def, bind_assoc] >>
  `gas_marked_exec T (ctx,func) (eval_iterator cx it) (es,s0)
     [] (INL vs) es (OK s0)` by
    (simp[gas_marked_exec_def, gas_marked_path_def] >>
     irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  drule gas_exempt_cert_bind_values >>
  simp[] >> disch_then irule >>
  simp[check_def, compatible_bound_def, vyperStateTheory.assert_def, bind_return,
       GSYM ignore_bind_def] >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[ignore_bind_def, vyperStateTheory.assert_def, bind_return]
QED
