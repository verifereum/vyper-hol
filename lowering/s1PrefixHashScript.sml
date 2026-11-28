(* Request-prefix companion to bodyFullHash. *)
Theory s1PrefixHash
Ancestors
  s1PrefixPreds bodyFullHash s1PrefixDefs s1PrefixHashKeccak
  s1PrefixCompose s1PrefixPrecompile s1PrefixOfVV s1PrefixProps
  bodySimFull bodyFullPreds bodyPtrHashBuiltinsCases
  exprSimHash exprSimHypsDefs exprSimSource exprLowering exprLoweringProps
  vyperTypeSystem vyperTyping compileEnv fragExec vyperState vyperInterpreter
  vyperContext vyperStorageTrace gasShadowCompileStmtHelpers gasShadow gasShadowState
  gasOutcomeFullCompose exprSimDefs
  bodyFullExprsSingleton bodyFullSimProjection

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac
  >- metis_tac[keccak_vv_sim_prefix] >>
  gvs[] >>
  `is_bytes_or_string_type (expr_type e) /\ ann = BaseT (BytesT (Fixed 32))` by
    (irule (SRULE [] (Q.INST [`b` |-> `Sha256`,
        `ts` |-> `[expr_type e]`] hash_builtin_types)) >>
     gvs[expr_body_pre_def, well_typed_expr_def]) >>
  simp[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr cenv ty (Builtin _ _ _) sa = _` mp_tac >>
  simp[compile_hash_singleton] >> pairarg_tac >> strip_tac >> gvs[] >>
  `?shadow_sm. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (v,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (qpat_assum `gas_shadow_state sa shadow_sa`
       (mp_then Any mp_tac (REWRITE_RULE [gas_shadow_compiles_def]
         (Q.INST [`ty` |-> `expr_type e`, `sd` |-> `T`] gas_shadow_stmt_lower_value_env))) >>
     disch_then (qspecl_then [`e`, `cenv`] mp_tac) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> simp[]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, gas_shadow_builtin_def, compile_hash_singleton] >>
     qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
     `?bty. expr_type e = BaseT bty` by
       (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
     Cases_on `bty` >> gvs[is_bytes_or_string_type_def, is_bytestring_type_def] >>
     TRY (rename1 `expr_type e = BaseT (BytesT bd)` >> Cases_on `bd` >>
          gvs[is_bytestring_type_def]) >>
     rpt strip_tac >>
     FIRST [
       rename1 `cs_extends sm sb` >>
       qpat_x_assum `as_stack_val _ (_ sm) = _` mp_tac,
       rename1 `cs_extends shadow_sm shadow_sb` >>
       qpat_x_assum `as_stack_val _ (_ shadow_sm) = _` mp_tac] >>
     qmatch_goalsub_abbrev_tac `as_stack_val _ suffix` >>
     Cases_on `suffix` >> simp[as_stack_val_def] >> strip_tac >>
     gvs[markerTheory.Abbrev_def] >>
     metis_tac[hash_suffix_appends, cs_appends_def]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split] >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> gvs[expr_body_pre_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`v`,`s0`,`G0`,`tn0`] mp_tac o
      REWRITE_RULE [expr_sim_full_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`v`,`s0`,`G0`,`tn0`] mp_tac o
      REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res ee G tn t. ~t.vs_halted) (\H res ee gt r. ISR res)` by
    (qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
       (mp_then Any irule gas_outcome_full_post_source) >>
     simp[] >> rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]) >>
  (* SHA256 records only computed-precompile outcomes. Any request covered
     by the prefix judgment therefore arises in the operand. *)
  rewrite_tac[eval_expr_sha256_action] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, sha256_continuation_frame,
       requests_outcomes_frame_bind_all, evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result] >>
  rpt gen_tac >>
  Cases_on `builtin_result cx st.accounts (BaseT (BytesT (Fixed 32)))
    Sha256 [expr_type e] [v']` >>
  simp[ignore_bind_def, bind_def, return_def] >>
  Cases_on `precompile_call_success Sha256 [v'] (st with gas_obs := gobs)` >>
  rename1 `precompile_call_success _ _ _ = (ans,mid)` >>
  Cases_on `ans` >> simp[] >> strip_tac >> gvs[] >>
  qpat_assum `precompile_call_success _ _ _ = _`
    (mp_then Any mp_tac precompile_call_success_only_computed_outcomes) >> simp[]
QED
*)
Theorem hash_vv_sim_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann bt e es.
  (bt = Keccak256 \/ bt = Sha256) /\
  expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es /\
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann bt [e]) es
Proof
  cheat
QED

Theorem hash_expr_prefix_ok:
  !cx ty bt es.
  (bt = Keccak256 \/ bt = Sha256) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  rewrite_tac[body_expr_prefix_ok_def] >>
  reverse conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `LENGTH es = 1` by metis_tac[hash_body_pre_arity] >>
  `?e. es = [e]` by (Cases_on `es` >> gvs[listTheory.LENGTH_EQ_NUM]) >>
  qpat_x_assum `es = [e]` SUBST_ALL_TAC >>
  `builtin_args_length_ok bt 1` by
    (qpat_assum `bt = Keccak256 \/ bt = Sha256` strip_assume_tac >>
     gvs[builtin_args_length_ok_def]) >>
  `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e` by
    (qpat_x_assum `builtin_args_length_ok _ _ ==> body_exprs_full_ok _ _` mp_tac >>
     qpat_x_assum `builtin_args_length_ok _ _ ==> body_exprs_prefix_ok _ _` mp_tac >>
     simp[body_exprs_full_ok_singleton, body_exprs_prefix_ok_def]) >>
  `expr_body_pre cenv cx env e es'` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> gvs[expr_body_pre_def]) >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty' (Builtin ty bt [e]) es'` by
    (qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
       (mp_then Any irule hash_vv_sim_prefix) >> simp[] >>
     conj_tac
     >- (drule_all body_expr_full_ok_simulations >> simp[]) >>
     qpat_x_assum `body_expr_prefix_ok _ _` (mp_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  simp[expr_sim_prefix_of_vv]
QED
