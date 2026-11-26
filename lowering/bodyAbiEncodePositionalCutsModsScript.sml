(* Real and shadow compiler cuts for one positional ABI snapshot. *)
Theory bodyAbiEncodePositionalCutsMods
Ancestors
  exprSimFullBundleProps gasShadowCompileStmtHelpers gasShadowCompileConvert
  gasShadowCompileHelpers gasShadowState gasShadowCompilePure gasShadowCompileBase
  gasShadow exprLowering exprLoweringProps compileEnv fragExec list

Triviality positional_cons:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv cenv (exprs_can_mutate cenv xs)
    (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
  compile_abi_encode_args compile_expr cenv xs ss = (svs,sb) ==>
  compile_abi_encode_args compile_expr cenv (e::xs) sa = (sv::svs,sb)
Proof
  simp[compile_abi_encode_args_def,Once compile_ext_call_args_def,
       comp_bind_def,comp_return_def]
QED

Triviality positional_cut_code:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (sv,ss) /\
  compile_abi_encode_args compile_expr cenv xs ss = (svs,sb) /\
  fn_has_code sa sb func ==>
  fn_has_code sa sm func /\ fn_has_code sm ss func /\
  fn_has_code sa ss func /\ fn_has_code ss sb func /\ ci_mono sa ss /\ ci_mono ss sb
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sa sm` by
    (qspec_then `sa` mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`] (cj 1 compile_expr_ci_mono)) >> simp[]) >>
  `ci_mono sm ss` by
    (qspecl_then [`ce`,`copy`,`ext_call_arg_value ty vv`,`sm`]
       mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `ci_mono ss sb` by
    (mp_tac (Q.INST [`f` |-> `compile_expr`,`st` |-> `ss`,`args` |-> `xs`]
       ci_mono_compile_abi_encode_args) >> simp[cj 1 compile_expr_ci_mono]) >>
  `ci_mono sa ss` by (irule ci_mono_trans >> qexists `sm` >> simp[]) >>
  `fn_has_code sa ss func /\ fn_has_code ss sb func` by
    (qspecl_then [`sa`,`ss`,`sb`,`func`] mp_tac fn_has_code_split >> fs[ci_mono_def]) >>
  qspecl_then [`sa`,`sm`,`ss`,`func`] mp_tac fn_has_code_split >> fs[ci_mono_def]
QED

Theorem positional_paired_cuts:
  compile_abi_encode_args compile_expr cenv (e::xs) sa = (all,sb) /\
  compile_abi_encode_args compile_expr (gas_shadow_env T cenv)
    (MAP gas_shadow_expr (e::xs)) sha = (all,shb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,sha,shb) ==>
  ?vv sm shm sv ss shs svs.
    all = sv::svs /\
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
    compile_snapshot_vv cenv (exprs_can_mutate cenv xs)
      (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
    compile_snapshot_vv (gas_shadow_env T cenv) (exprs_can_mutate cenv xs)
      (ext_call_arg_value (lowered_value_type cenv e) vv) shm = (sv,shs) /\
    compile_abi_encode_args compile_expr cenv xs ss = (svs,sb) /\
    compile_abi_encode_args compile_expr (gas_shadow_env T cenv)
      (MAP gas_shadow_expr xs) shs = (svs,shb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,ss,sha,shs) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sm,sha,shm) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (ss,sb,shs,shb) /\
    fn_has_code sm ss func /\ ci_mono sa ss /\ ci_mono ss sb
Proof
  simp[expr_sim_full_code_def] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) sha = (shvv,shm)` >>
  `shvv = vv /\ gas_shadow_state sm shm` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`,`ty` |-> `expr_type e`,`e` |-> `e`,`sd` |-> `T`]
       gas_shadow_stmt_compile_expr_env) >>
     simp[gas_shadow_compiles_def] >> disch_then (qspecl_then [`sa`,`sha`] mp_tac) >> simp[]) >>
  qpat_x_assum `shvv = vv` SUBST_ALL_TAC >>
  qabbrev_tac `copy = exprs_can_mutate cenv xs` >>
  qabbrev_tac `v = ext_call_arg_value (lowered_value_type cenv e) vv` >>
  Cases_on `compile_snapshot_vv cenv copy v sm` >>
  rename1 `compile_snapshot_vv cenv copy v sm = (sv,ss)` >>
  Cases_on `compile_snapshot_vv (gas_shadow_env T cenv) copy v shm` >>
  rename1 `compile_snapshot_vv (gas_shadow_env T cenv) copy v shm = (shsv,shs)` >>
  `shsv = sv /\ gas_shadow_state ss shs` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`,`copy_flag` |-> `copy`,`vv` |-> `v`]
       gas_shadow_compiles_snapshot_vv) >>
     simp[gas_shadow_compiles_def] >> disch_then (qspecl_then [`sm`,`shm`] mp_tac) >>
     fs[]) >>
  qpat_x_assum `shsv = sv` SUBST_ALL_TAC >>
  Cases_on `compile_abi_encode_args compile_expr cenv xs ss` >>
  rename1 `compile_abi_encode_args compile_expr cenv xs ss = (svs,end)` >>
  Cases_on `compile_abi_encode_args compile_expr (gas_shadow_env T cenv)
            (MAP gas_shadow_expr xs) shs` >>
  rename1 `compile_abi_encode_args _ (gas_shadow_env T _) _ shs = (shsvs,shend)` >>
  qunabbrev_tac `copy` >> qunabbrev_tac `v` >>
  drule_at (Pat `compile_expr cenv _ e sa = _`) positional_cons >>
  disch_then drule >> disch_then drule >> strip_tac >>
  `all = sv::shsvs /\ shb = shend` by
    (qpat_assum `compile_abi_encode_args _ _ (_::_) sha = _` mp_tac >>
     qpat_assum `compile_abi_encode_args _ _ _ shs = _` mp_tac >>
     rewrite_tac[compile_abi_encode_args_def] >> strip_tac >>
     simp[Once compile_ext_call_args_def,comp_bind_def,comp_return_def,
          gas_shadow_expr_can_mutate] >> fs[]) >>
  `all = sv::svs /\ sb = end` by fs[] >>
  qpat_x_assum `shb = shend` SUBST_ALL_TAC >>
  qpat_x_assum `sb = end` SUBST_ALL_TAC >>
  `shsvs = svs` by fs[] >> qpat_x_assum `shsvs = svs` SUBST_ALL_TAC >>
  drule_at (Pat `compile_expr cenv _ e sa = _`) positional_cut_code >>
  disch_then drule >> disch_then drule >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_at (Pat `compile_expr _ _ (gas_shadow_expr _) sha = _`)
    (SIMP_RULE (srw_ss()) []
       (Q.INST [`e` |-> `gas_shadow_expr e`, `cenv` |-> `gas_shadow_env T cenv`,
                `xs` |-> `MAP gas_shadow_expr xs`] positional_cut_code)) >>
  disch_then drule >> disch_then drule >>
  disch_then (qspec_then `shadow_func` mp_tac) >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `shs` >> fs[]
QED
