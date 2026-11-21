(* AsWeiValue composes the child's companion with a request-free suffix. *)
Theory s1PrefixWordWei
Ancestors
  s1PrefixCompose s1PrefixDefs s1PrefixFrame s1PrefixProps
  bodyFullBuiltinWordWeiPrefix exprBodyPreProps bodyFullPreds bodySimFull
  exprSimSource exprSimDefs exprSimWordBuiltins exprSimUnopProps
  exprLoweringProps gasOutcomeFullCompose gasContext gasExplicitSites gasShadowCompileStmtHelpers
  fragExec exprSimHypsDefs vyperInterpreter vyperStorageTrace
  vyperStorageFootprint vyperState vyperAST vyperCallOutcomeFrame
  vyperStatePreservation compileEnv list sum

Theorem word_wei_sim_prefix:
  (!e. expr_body_pre cenv cx env e es ==>
       expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx (expr_type e) e es /\
       expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx (expr_type e) e es) /\
  expr_body_pre cenv cx env (Builtin ann (AsWeiValue dn) args) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (AsWeiValue dn) args) es
Proof
  strip_tac >> drule as_wei_value_argument_shape >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> conj_tac
     >- metis_tac[expr_body_pre_static_facts] >>
     qexistsl_tac [`BaseT (UintT 256)`, `[e]`, `AsWeiValue dn`, `es`] >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  PURE_REWRITE_TAC[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all as_wei_value_lower_pair >> strip_tac >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by
    (qpat_assum `lower_value _ _ _ e sa = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     simp[is_word_type_def] >> metis_tac[]) >>
  `cs_extends s1 sb` by
    metis_tac[straight_fresh_cs_extends, straight_fresh_as_wei_value_int] >>
  `fn_has_code sa s1 func` by metis_tac[fn_has_code_split] >>
  `cs_extends shadow_sa sh1 /\ cs_extends sh1 shadow_sb` by
    metis_tac[compile_expr_grows, straight_fresh_cs_extends,
              straight_fresh_as_wei_value_int] >>
  `fn_has_code shadow_sa sh1 shadow_func` by metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e es`
    (drule_all o REWRITE_RULE[expr_sim_full_def]) >>
  strip_tac >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ e es`
    (drule_all o REWRITE_RULE[expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  strip_tac >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res ee G tn t. ~t.vs_halted) (\H res ee gt r. ISR res)` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
       (mp_then Any irule gas_outcome_full_post_source) >>
     simp[] >> rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]) >>
  rewrite_tac[as_wei_value_source_bind] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. ~t.vs_halted) _`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[] >> rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_def]
  >~ [`requests_outcomes_frame _`]
  >- (irule requests_outcomes_frame_bind_all >>
      simp[evaluate_requests_outcomes_frame, requests_outcomes_frame_def,
           state_rel_frame_result] >>
      rpt strip_tac >> drule read_result_state >> simp[])
  >> rpt strip_tac >> irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_def] >>
  qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> ~t.vs_halted`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[GSYM storage_trace_domain_def]
QED
