Theory bodyMemBiECRecoverCompose
Ancestors
  bodyMemBiECRecoverPaths bodyArgsMemory exprSimPrecompiles exprSimWordArgs
  exprSimMemDefs gasOutcome gasSummary gasSummaryCompose gasExemptCert
  fragGasMode fragGasPath exprSimDefs vyperInterpreter vyperState list
  exprSimProps exprLowering exprLoweringProps exprSimHypsDefs vyperTyping
  vyperAST vyperTypeSystem compileEnv loweringStateRelDefs rich_list builtinMisc loweringPosts
  exprBopLowering vyperContext vyperValue vyperTypeInvariants valueEncoding
  integer_word words byte context emitHelper emitHelperProps venomExecSemantics
  venomInst venomState venomMemDefs venomCallOracleDefs extCallOracle
  exprSimSource fragExec vyperEvalExprPreservesScopesDom gasStorage
  vyperStorageFootprint vyperStorageTrace

(* Memory-mode counterpart of eval_exprs_suffix in exprSimPrecompiles. *)
Theorem ecrecover_eval_exprs_suffix_mem:
  gas_outcome T tops (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H rr ee t. ?vs. rr = INL vs /\ P H vs ee t)
    (\H rr ee r. wb_args_exit rr r) /\
  (!vs. storage_trace_frame (k vs)) /\
  (!H exc ee r. wb_args_exit (INR exc) r ==> R H (INR exc) ee r) /\
  (!gs vs ee t.
     eval_exprs cx args (es with gas_obs := gs) = (INL vs, ee) /\
     ee.gas_obs = [] /\ ~t.vs_halted /\
     (?H. valid_horizon cx st0 H ee.storage_trace) /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> P H vs ee t) ==>
     ?marks. gas_summary_at T (ctx,func) marks (k vs) (ee,t)
       (\res fin t. !H. valid_horizon cx st0 H fin.storage_trace ==>
          Q H res fin t)
       (\res fin r. !H. valid_horizon cx st0 H fin.storage_trace ==>
          R H res fin r)) ==>
  gas_outcome T tops (ctx,func) cx st0 (bind (eval_exprs cx args) k) (es,s0) Q R
Proof
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >> simp[])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (qexists_tac `marks` >> disj1_tac >>
           irule gas_bad_storage_at_bind_left >> simp[] >>
           irule gas_bad_storage_at_counted_prefix >> metis_tac[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def]
      >- (qpat_x_assum `(\res ee t. _) _ _ _`
            (assume_tac o SIMP_RULE (srw_ss()) []) >>
          qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> ?vs. _`
            (drule_then (qx_choose_then `vs` strip_assume_tac)) >>
          qpat_x_assum `res = INL vs` SUBST_ALL_TAC >>
          qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
          qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> ?vs. _`
            (assume_tac o SIMP_RULE (srw_ss()) []) >>
          `eval_exprs cx args
             (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL vs, es_end with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          qpat_x_assum `!gs vs ee t. _`
            (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `vs`,
                          `es_end with gas_obs := []`, `t`] mp_tac) >>
          (impl_tac >- (asm_simp_tac (srw_ss()) [] >> metis_tac[])) >>
          strip_tac >>
          rename1 `gas_summary_at T _ right _ _ _ _` >>
          qexists_tac `marks ++ right` >> disj2_tac >> disj1_tac >>
          qpat_x_assum `gas_summary_at T _ right _ _ _ _`
            (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
          disch_then (qx_choosel_then [`fres`, `fin`, `fr`]
            (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
          drule_all gas_marked_exec_bind_normal >> strip_tac >>
          rewrite_tac[gas_summary_at_def] >>
          qexistsl_tac [`fres`, `fin`, `fr`] >> asm_rewrite_tac[]) >>
      qpat_x_assum `(\res ee r. _) _ _ _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      `wb_args_exit res r` by metis_tac[] >>
      Cases_on `res` >> gvs[wb_args_exit_def] >>
      rename1 `expr_exit (INR exc) r` >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
      disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      BETA_TAC >> rpt strip_tac >>
      qpat_x_assum `!H exc ee r. _ ==> R _ _ _ _` irule >>
      gvs[wb_args_exit_def]) >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qabbrev_tac `a = eval_exprs cx args` >>
  `ignore_bind (bind a k) (return ()) =
   bind a (\v. ignore_bind (k v) (return ()))` by
    simp[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  pop_assum SUBST1_TAC >>
  metis_tac[gas_exempt_cert_error_values]
QED

Theorem ecrecover_expr_sim_mem:
  expr_body_pre cenv cx env (Builtin ann ECRecover args) es /\
  (!arg_ty. typed_args_ready_mem ctx func cenv cx arg_ty
     (expr_sim_inv cenv cx env) args) ==>
  expr_sim_mem ctx func cenv cx ty (Builtin ann ECRecover args) es
Proof
  strip_tac >> drule ecrecover_pre_types >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
         expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)` by
    (rpt strip_tac
     >- (qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
           (mp_then Any mp_tac expr_body_pre_builtin_arg) >>
         simp[] >> disch_then irule >> simp[]) >>
     gvs[EVERY_MEM]) >>
  `wb_args_shape cenv (\e. ty) args` by metis_tac[typed_stack_args_shape] >>
  `well_typed_builtin_app ann ECRecover (MAP expr_type args)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  rewrite_tac[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all lower_value_ecrecover_args >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sb` by metis_tac[compile_ecrecover_extends] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!es gs. expr_sim_inv cenv cx env es ==>
           expr_sim_inv cenv cx env (es with gas_obs := gs)` by simp[] >>
  `typed_args_ready_mem ctx func cenv cx (\e. ty)
     (expr_sim_inv cenv cx env) args` by simp[] >>
  drule_all lower_typed_args_sim_mem >> strip_tac >>
  drule_then (fn th => rewrite_tac[th]) eval_expr_ecrecover_read_action >>
  irule expr_sim_mem_word_outcome >> simp[expr_type_def, is_word_type_def] >>
  irule ecrecover_eval_exprs_suffix_mem >> rpt conj_tac
  >~ [`storage_trace_frame _`]
  >- (gen_tac >>
      `!(w:value). storage_trace_frame
             (do precompile_call_success ECRecover; return w od)` by
        simp[storage_trace_frame_ignore_bind, storage_trace_frame_return,
             storage_trace_frame_precompile_call_success] >>
      simp[storage_trace_frame_def] >> rpt gen_tac >>
      Cases_on `builtin_result cx st.accounts ann ECRecover (MAP expr_type args) vs` >>
      simp[] >>
      qpat_x_assum `!w. storage_trace_frame _` (qspec_then `x` mp_tac) >>
      disch_then (mp_tac o Q.SPECL [`st`, `observations`] o
                  PURE_ONCE_REWRITE_RULE [storage_trace_frame_def]) >>
      simp[])
  >~ [`wb_args_exit (INR _) _`] >- simp[wb_args_exit_def] >>
  qexists_tac `\H vs ee t. typed_args_post H ctx func cenv cx es sa s0 ee args
                 [h;v;r;sig] vs t /\ t.vs_current_bb = sm.cs_current_bb /\
                 t.vs_inst_idx = LENGTH sm.cs_current_insts /\
                 alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  BETA_TAC >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `storage_trace_frame (eval_exprs cx args)` by
    simp[evaluate_storage_trace_frame] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_all valid_horizon_frame >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) args vs` by
    (irule stack_args_values_typed_body >>
     qexistsl_tac [`cenv`, `env`, `es with gas_obs := gs`, `ee`] >>
     simp[] >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  drule_all ecrecover_typed_result >>
  disch_then (qspec_then `ee.accounts` strip_assume_tac) >>
  gvs[typed_args_post_def] >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ee t` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `ee.outcomes = SOME t.vs_outcomes` by
    (qpat_x_assum `stmt_state_rel H _ _ _ _ ee t` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[stmt_state_rel_def, state_rel_def]) >>
  `!x. MEM (Var x) [h;v;r;sig] ==> not_fresh_at sm x` by
    (gvs[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `builtin_result _ _ _ _ _ _ = INL (AddressV addr)` >>
  Cases_on `t.vs_outcomes`
  >- (`~(?co rest. t.vs_outcomes = co::rest /\ co.co_success)` by gvs[] >>
      drule_all ecrecover_failure_path_mem >> strip_tac >>
      qexists_tac `REPLICATE n F` >> rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR (Error (RuntimeError "precompile failed"))`, `ee`,
                    `Abort a u`] >>
      asm_simp_tac (srw_ss()) [gas_marked_exec_def, exit_result_def,
        expr_exit_def, ignore_bind_def, bind_def, ecrecover_source_outcome_step]) >>
  rename1 `t.vs_outcomes = co::rest` >> Cases_on `co.co_success`
  >- (`~EXISTS expr_has_effect [ah;av;ar;asig] ==>
        pure_frame cenv func es sa s0 t` by
        (strip_tac >> first_assum match_mp_tac >> gvs[]) >>
      drule_all ecrecover_success_path_mem >> strip_tac >>
      qabbrev_tac `es2 = ee with outcomes := SOME rest` >>
      `es2.storage_trace = ee.storage_trace` by simp[Abbr `es2`] >>
      `es2 with gas_obs := [] = es2` by
        gvs[Abbr `es2`, evaluation_state_component_equality] >>
      qexists_tac `REPLICATE n F` >> rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INL (AddressV addr)`, `es2`, `OK u`] >>
      rewrite_tac[gas_marked_exec_def, LENGTH_REPLICATE,
                  gas_explicit_replicate_false, APPEND] >>
      BETA_TAC >> pop_assum SUBST1_TAC >> conj_tac
      >- (asm_simp_tac (srw_ss()) [Abbr `es2`, ignore_bind_def, bind_def,
            ecrecover_source_outcome_step, return_def]) >>
      disj1_tac >> qexists_tac `u` >> simp[] >>
      qx_gen_tac `H2` >> strip_tac >>
      `valid_horizon cx st0 H2 ee.storage_trace` by fs[] >>
      `stmt_state_rel H2 ctx func cenv cx ee t /\
       storage_well_formed_on cx ee (FST H2)` by
        (qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
           (qspec_then `H2` mp_tac) >> simp[]) >>
      first_x_assum (fn th =>
        if is_forall (concl th) andalso
           can (find_term (fn tm => is_const tm andalso
                  fst (dest_const tm) = "expr_post")) (concl th)
        then mp_tac (Q.SPEC `H2` th) else NO_TAC) >>
      impl_tac >- simp[] >>
      simp[Abbr `addr`] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `~(?co rest. t.vs_outcomes = co::rest /\ co.co_success)` by gvs[] >>
  drule_all ecrecover_failure_path_mem >> strip_tac >>
  qexists_tac `REPLICATE n F` >> rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "precompile failed"))`,
                `ee with outcomes := SOME rest`, `Abort a u`] >>
  asm_simp_tac (srw_ss()) [gas_marked_exec_def, exit_result_def,
    expr_exit_def, ignore_bind_def, bind_def, ecrecover_source_outcome_step]
QED
