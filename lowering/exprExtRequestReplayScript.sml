Theory exprExtRequestReplay
Ancestors
  exprExtRequestReplayPrimitives exprExtRequestReplayAlgebra
  supportedExprTraverse vyperInterpreter
  vyperState vyperAST list

Theorem extrequest_replay_leaf:
  extrequest_success_replay (eval_expr cx (Name ann id)) /\
  extrequest_success_replay (eval_expr cx (Literal ann lit)) /\
  extrequest_success_replay (eval_expr cx (TopLevelName ann (src,id))) /\
  extrequest_success_replay (eval_expr cx (FlagMember ann nsid mid))
Proof
  rpt conj_tac >> irule extrequest_equivariant_replay
  >- (simp[Once evaluate_def, ignore_bind_def] >>
      irule extrequest_obs_bind >> simp[extrequest_obs_get_scopes] >>
      gen_tac >> irule extrequest_obs_bind >> simp[extrequest_obs_type_check])
  >- simp[Once evaluate_def]
  >- simp[Once evaluate_def, extrequest_obs_lookup_global]
  >> simp[Once evaluate_def, extrequest_obs_lookup_flag]
QED

Theorem extrequest_replay_bind_guarded[local]:
  extrequest_success_replay f /\
  (!s a m. f s = (INL a,m) ==> extrequest_success_replay (g a)) ==>
  extrequest_success_replay (bind f g)
Proof
  simp[extrequest_success_replay_def] >> rpt strip_tac >>
  gvs[bind_def, AllCaseEqs()] >>
  rename1 `f s = (INL a,m)` >>
  qpat_x_assum `!s a m. f s = (INL a,m) ==> !s' x t. _` drule >>
  disch_then (qspecl_then [`m`,`x`,`t`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `more` assume_tac) >>
  qpat_x_assum `!s x t. f s = (INL x,t) ==> ?used. _` drule >>
  disch_then (qx_choose_then `used` assume_tac) >>
  qexists `used ++ more` >> gen_tac >>
  qpat_assum `!tail. f _ = _` (qspec_then `more ++ tail` assume_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[bind_def, Excl "APPEND_ASSOC"]
QED

Theorem extrequest_replay_primitives[local]:
  extrequest_success_replay (type_check b msg) /\
  extrequest_success_replay (lift_sum v) /\
  extrequest_success_replay get_accounts /\
  extrequest_success_replay (conditional_result cx r) /\
  extrequest_success_replay (select_result cx ty r sub) /\
  extrequest_success_replay (result_array_length cx r) /\
  extrequest_success_replay (extend_place cx p sub) /\
  extrequest_success_replay (get_place r) /\
  extrequest_success_replay (read_result cx r) /\
  extrequest_success_replay (lookup_global cx src id) /\
  extrequest_success_replay (precompile_call_success bt)
Proof
  rpt conj_tac >> irule extrequest_equivariant_replay >>
  simp[extrequest_obs_type_check, extrequest_obs_lift_sum,
    extrequest_obs_get_accounts, extrequest_obs_conditional,
    extrequest_obs_select, extrequest_obs_array_length, extrequest_obs_extend,
    extrequest_obs_get_place, extrequest_obs_read_result,
    extrequest_obs_lookup_global, extrequest_obs_precompile]
QED

Theorem extrequest_evaluate_replay:
  (!cx s. eval_stmt cx s = eval_stmt cx s) /\
  (!cx ss. eval_stmts cx ss = eval_stmts cx ss) /\
  (!cx it. eval_iterator cx it = eval_iterator cx it) /\
  (!cx ty id body vs. eval_for cx ty id body vs = eval_for cx ty id body vs) /\
  (!cx e. ~supported_expr_exists expr_effect_root e ==>
    extrequest_success_replay (eval_expr cx e)) /\
  (!cx es. ~supported_exprs_exists expr_effect_root es ==>
    extrequest_success_replay (eval_exprs cx es)) /\
  (!cx bt. ~supported_target_exists expr_effect_root bt ==>
    extrequest_success_replay (eval_base_place cx bt)) /\
  (!cx tgt. ~supported_target_exists expr_effect_root tgt ==>
    extrequest_success_replay (eval_target_place cx tgt)) /\
  (!cx tgt v. assign_tuple_targets cx tgt v = assign_tuple_targets cx tgt v) /\
  (!cx tgts vs. assign_tuple_target_list cx tgts vs = assign_tuple_target_list cx tgts vs) /\
  (!cx es. ~supported_exprs_exists expr_effect_root es ==>
    extrequest_success_replay (eval_expr_results cx es))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[supported_expr_exists_def, expr_effect_root_def] >> rpt gen_tac
  >- simp[extrequest_replay_leaf]
  >- simp[extrequest_replay_leaf]
  >- simp[extrequest_replay_leaf]
  >- suspend "if_exp"
  >- simp[extrequest_replay_leaf]
  >- suspend "struct"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "builtin"
  >- suspend "type_builtin"
  >- simp[Once evaluate_def, extrequest_replay_return]
  >- suspend "exprs_cons"
  >- suspend "base_name"
  >- simp[Once evaluate_def, extrequest_replay_primitives]
  >- suspend "base_attribute"
  >- suspend "base_subscript"
  >- suspend "target"
  >- simp[Once evaluate_def, extrequest_replay_return]
  >> suspend "results_cons"
QED

Resume extrequest_evaluate_replay[attribute]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule extrequest_replay_bind >> simp[extrequest_replay_primitives, extrequest_replay_return,
       extrequest_replay_raise]
QED

Resume extrequest_evaluate_replay[struct]:
  rpt strip_tac >>
  fs[supported_fields_exists_every, supported_exprs_exists_every,
     listTheory.EVERY_MAP, combinTheory.o_DEF] >>
  simp[Once evaluate_def] >> irule extrequest_replay_bind >>
  simp[extrequest_replay_primitives, extrequest_replay_return,
       extrequest_replay_raise]
QED

Resume extrequest_evaluate_replay[if_exp]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule extrequest_replay_bind_guarded >> simp[] >>
  rpt strip_tac >> irule extrequest_replay_bind >>
  simp[extrequest_replay_primitives, extrequest_replay_return,
       extrequest_replay_raise] >>
  irule extrequest_replay_switch >> metis_tac[]
QED

Resume extrequest_evaluate_replay[subscript]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule extrequest_replay_bind_guarded >> simp[] >>
  rpt strip_tac >> irule extrequest_replay_bind >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> simp[] >> irule extrequest_replay_bind >>
  simp[extrequest_replay_primitives, extrequest_replay_return,
       extrequest_replay_raise]
QED

Resume extrequest_evaluate_replay[base_name]:
  simp[Once evaluate_def, ignore_bind_def] >>
  irule extrequest_equivariant_replay >>
  irule extrequest_obs_bind >> simp[extrequest_obs_get_scopes] >>
  gen_tac >> irule extrequest_obs_bind >> simp[extrequest_obs_type_check]
QED

Resume extrequest_evaluate_replay[base_attribute]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule extrequest_replay_bind >>
  simp[extrequest_replay_primitives, extrequest_replay_return]
QED

Resume extrequest_evaluate_replay[target]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule extrequest_replay_bind >>
  simp[extrequest_replay_primitives, extrequest_replay_return]
QED

Resume extrequest_evaluate_replay[results_cons]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule extrequest_replay_bind_guarded >> simp[] >>
  rpt strip_tac >> irule extrequest_replay_bind >>
  simp[extrequest_replay_return] >> metis_tac[]
QED

Resume extrequest_evaluate_replay[exprs_cons]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule extrequest_replay_bind_guarded >> simp[] >>
  rpt strip_tac >> irule extrequest_replay_bind_guarded >>
  simp[extrequest_replay_primitives] >>
  rpt strip_tac >> irule extrequest_replay_bind >>
  simp[extrequest_replay_return] >> metis_tac[]
QED

Resume extrequest_evaluate_replay[base_subscript]:
  rpt strip_tac >> simp[Once evaluate_def] >>
  irule extrequest_replay_bind_guarded >> simp[] >>
  rpt strip_tac >> irule extrequest_replay_bind_guarded >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> irule extrequest_replay_bind >>
  simp[extrequest_replay_primitives, extrequest_replay_return]
QED

Resume extrequest_evaluate_replay[type_builtin]:
  rpt strip_tac >> simp[Once evaluate_def, ignore_bind_def] >>
  irule extrequest_replay_bind_guarded >>
  simp[extrequest_replay_primitives] >>
  rpt strip_tac >> irule extrequest_replay_bind >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> simp[] >> irule extrequest_replay_bind >>
  simp[extrequest_replay_primitives, extrequest_replay_return]
QED

Resume extrequest_evaluate_replay[builtin]:
  rpt strip_tac >> simp[Once evaluate_def, ignore_bind_def] >>
  irule extrequest_replay_bind_guarded >>
  simp[extrequest_replay_primitives] >>
  rpt strip_tac >> irule extrequest_replay_bind >>
  simp[extrequest_replay_return] >>
  Cases_on `bt = Len`
  >- (simp[] >> irule extrequest_replay_bind >> reverse conj_tac
      >- (first_x_assum irule >> goal_assum (drule_at Any) >>
          fs[supported_exprs_exists_every, listTheory.EVERY_MEM] >>
          conj_tac >- (Cases_on `es` >>
            gvs[type_check_def, assert_def, return_def, raise_def,
                vyperContextTheory.builtin_args_length_ok_def] >> metis_tac[listTheory.MEM]) >>
          goal_assum (drule_at Any)) >>
      gen_tac >> simp[] >> irule extrequest_replay_bind >>
      simp[extrequest_replay_primitives, extrequest_replay_return]) >>
  Cases_on `bt = Env MsgGas` >> simp[]
  >- simp[extrequest_replay_gas_read] >>
  irule extrequest_replay_bind_guarded >> reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> simp[] >> irule extrequest_replay_bind >>
  simp[extrequest_replay_primitives] >>
  gen_tac >> simp[] >> irule extrequest_replay_bind >>
  simp[extrequest_replay_primitives] >>
  gen_tac >> simp[] >> irule extrequest_replay_bind >>
  simp[extrequest_replay_primitives, extrequest_replay_return]
QED

Finalise extrequest_evaluate_replay

Theorem extrequest_pure_expr_success_replay:
  ~expr_has_effect e /\ eval_expr cx e s = (INL x,t) ==>
  ?used. !tail. eval_expr cx e (s with gas_obs := used ++ tail) =
    (INL x,t with gas_obs := tail)
Proof
  strip_tac >>
  `extrequest_success_replay (eval_expr cx e)` by
    fs[expr_has_effect_def, extrequest_evaluate_replay] >>
  metis_tac[extrequest_success_replay_def]
QED

Theorem extrequest_pure_exprs_success_replay:
  EVERY (\e. ~expr_has_effect e) es /\ eval_exprs cx es s = (INL x,t) ==>
  ?used. !tail. eval_exprs cx es (s with gas_obs := used ++ tail) =
    (INL x,t with gas_obs := tail)
Proof
  strip_tac >>
  `extrequest_success_replay (eval_exprs cx es)` by
    fs[expr_has_effect_def, supported_exprs_exists_every,
       combinTheory.o_DEF, extrequest_evaluate_replay] >>
  metis_tac[extrequest_success_replay_def]
QED

Theorem extrequest_pure_results_success_replay:
  EVERY (\e. ~expr_has_effect e) es /\ eval_expr_results cx es s = (INL x,t) ==>
  ?used. !tail. eval_expr_results cx es (s with gas_obs := used ++ tail) =
    (INL x,t with gas_obs := tail)
Proof
  strip_tac >>
  `extrequest_success_replay (eval_expr_results cx es)` by
    fs[expr_has_effect_def, supported_exprs_exists_every,
       combinTheory.o_DEF, extrequest_evaluate_replay] >>
  metis_tac[extrequest_success_replay_def]
QED

Theorem extrequest_results_prefix_replay:
  EVERY (\e. ~expr_has_effect e) es /\
  eval_expr_results cx es (start with gas_obs := gs) = (INL rs,fin) ==>
  ?used. !tail.
    eval_expr_results cx es (start with gas_obs := used ++ tail) =
      (INL rs,fin with gas_obs := tail)
Proof
  strip_tac >> drule_all extrequest_pure_results_success_replay >> simp[]
QED

Theorem extrequest_expr_prefix_replay:
  ~expr_has_effect e /\
  eval_expr cx e (start with gas_obs := gs) = (INL r,fin) ==>
  ?used. !tail.
    eval_expr cx e (start with gas_obs := used ++ tail) =
      (INL r,fin with gas_obs := tail)
Proof
  strip_tac >> drule_all extrequest_pure_expr_success_replay >> simp[]
QED

Theorem extrequest_exprs_prefix_replay:
  EVERY (\e. ~expr_has_effect e) es /\
  eval_exprs cx es (start with gas_obs := gs) = (INL rs,fin) ==>
  ?used. !tail.
    eval_exprs cx es (start with gas_obs := used ++ tail) =
      (INL rs,fin with gas_obs := tail)
Proof
  strip_tac >> drule_all extrequest_pure_exprs_success_replay >> simp[]
QED
