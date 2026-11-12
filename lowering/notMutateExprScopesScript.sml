Theory notMutateExprScopes
Ancestors
  exprLowering vyperInterpreter vyperLocalAccessFrame
  vyperState vyperContext vyperMisc pair sum
  vyperScopePreservation vyperStatePreservation vyperPlaceFrames
  vyperCallFrame vyperCallOutcomeFrame vyperCreateFrame rich_list

Theorem nonmutating_exprs_every[local]:
  !es cenv. ~exprs_can_mutate cenv es <=>
    EVERY (\e. ~expr_can_mutate cenv e) es
Proof
  Induct >> simp[expr_can_mutate_def]
QED

Theorem nonmutating_named_map[local]:
  !kes cenv. named_exprs_can_mutate cenv kes =
    exprs_can_mutate cenv (MAP SND kes)
Proof
  Induct >> simp[expr_can_mutate_def, pairTheory.FORALL_PROD]
QED

Theorem nonmutating_scopes_mutual[local]:
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tv:type_value) (id:string)
    (body:stmt list) (vs:eval_result list). T) /\
  (!cx e cenv s v s'. ~expr_can_mutate cenv e /\
    eval_expr cx e s = (INL v,s') ==> s'.scopes = s.scopes) /\
  (!cx es cenv s v s'. ~exprs_can_mutate cenv es /\
    eval_exprs cx es s = (INL v,s') ==> s'.scopes = s.scopes) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T) /\
  (!cx es cenv s v s'. ~exprs_can_mutate cenv es /\
    eval_expr_results cx es s = (INL v,s') ==> s'.scopes = s.scopes)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[expr_can_mutate_def]
  >- suspend "name"
  >- suspend "global"
  >- suspend "flag"
  >- suspend "ifexp"
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >- suspend "struct"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "builtin"
  >- suspend "typebuiltin"
  >- suspend "send"
  >- suspend "extcall"
  >- suspend "intcall"
  >- suspend "rawcall"
  >- suspend "rawcalldata"
  >- suspend "rawlog"
  >- suspend "rawrevert"
  >- suspend "selfdestruct"
  >- suspend "create"
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >- suspend "exprs"
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >> suspend "results"
QED

Resume nonmutating_scopes_mutual[name]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
QED
Resume nonmutating_scopes_mutual[global]:
  rpt strip_tac >> gvs[Once evaluate_def] >>
  metis_tac[lookup_global_scopes]
QED
Resume nonmutating_scopes_mutual[flag]:
  rpt strip_tac >> gvs[Once evaluate_def] >>
  metis_tac[lookup_flag_mem_scopes]
QED
Resume nonmutating_scopes_mutual[ifexp]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, switch_BoolV_def,
      AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac conditional_result_state >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED
Resume nonmutating_scopes_mutual[struct]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def,
      nonmutating_named_map] >> metis_tac[]
QED
Resume nonmutating_scopes_mutual[subscript]:
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED
Resume nonmutating_scopes_mutual[attribute]:
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Resume nonmutating_scopes_mutual[builtin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (Cases_on `bt = Len` >> rpt gen_tac >> strip_tac >>
      Cases_on `bt = Env MsgGas` >>
      Cases_on `bt = Bop In \/ bt = Bop NotIn` >>
      Cases_on `evaluate_type (get_tenv cx) (expr_type (EL 1 es))` >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, lift_option_type_def, AllCaseEqs()] >>
      imp_res_tac result_array_length_state >>
      imp_res_tac next_gas_reading_state >>
      imp_res_tac precompile_call_success_state >>
      imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >> gvs[] >>
      Cases_on `es` >>
      gvs[builtin_args_length_ok_def, expr_can_mutate_def] >> metis_tac[]) >>
  simp[Once evaluate_def, type_check_def, assert_def, bind_def,
       ignore_bind_def, raise_def]
QED
Resume nonmutating_scopes_mutual[typebuiltin]:
  rpt strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED
Resume nonmutating_scopes_mutual[send]:
  rpt gen_tac >> strip_tac >>
  Cases_on `LENGTH es = if has_gas then 3 else 2` >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac eval_send_preserves_non_accounts >>
  gvs[type_check_def, assert_def, return_def] >> metis_tac[]
QED
Resume nonmutating_scopes_mutual[extcall]:
  rpt strip_tac >>
  `~exprs_can_mutate cenv (TAKE 1 es) /\
   ~exprs_can_mutate cenv (TAKE (LENGTH (FST (SND sig))) (DROP 1 es)) /\
   ~exprs_can_mutate cenv (DROP (LENGTH (FST (SND sig)) + 1) es)` by
    (gvs[nonmutating_exprs_every] >> metis_tac[EVERY_TAKE, EVERY_DROP]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac eval_ext_call_preserves_non_accounts >>
  imp_res_tac read_results_state >> gvs[] >> metis_tac[]
QED
Resume nonmutating_scopes_mutual[intcall]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s t s1 ts t1 s2 tup t2 s3 t3 s4 vs t4 s5 prev t5 s6 t6. _` kall_tac >>
  rule_assum_tac (SRULE [type_check_def, assert_def, lift_option_type_def,
                        option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, lift_option_type_def, option_CASE_rator,
       return_def, raise_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac finally_set_scopes >>
  imp_res_tac (call_cleanup_scopes |>
    Q.INST [`is_view` |-> `mut = View \/ mut = Pure`] |>
    SRULE [unlock_if_nr_def]) >>
  imp_res_tac read_results_state >>
  gvs[get_scopes_def] >>
  gvs[return_def, push_function_def] >> metis_tac[]
QED
Resume nonmutating_scopes_mutual[rawcall]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, type_check_def, assert_def, lift_option_type_def,
       option_CASE_rator] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[]
QED
Resume nonmutating_scopes_mutual[rawcalldata]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, type_check_def, assert_def, lift_option_type_def,
       option_CASE_rator] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[]
QED
Resume nonmutating_scopes_mutual[rawlog]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, check_def, type_check_def, assert_def, lift_option_def,
       lift_option_type_def, push_log_def, option_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >> metis_tac[]
QED
Resume nonmutating_scopes_mutual[rawrevert]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, check_def, type_check_def, assert_def,
       lift_option_type_def, option_CASE_rator]
QED
Resume nonmutating_scopes_mutual[selfdestruct]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, check_def, type_check_def, assert_def, lift_option_def,
       lift_option_type_def, get_accounts_def, option_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
  Cases_on `cx.txn.created_in_tx` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()]
QED
Resume nonmutating_scopes_mutual[create]:
  rpt strip_tac >>
  `!n. ~exprs_can_mutate cenv (TAKE n es)` by
    metis_tac[nonmutating_exprs_every, EVERY_TAKE] >>
  `!n. ~exprs_can_mutate cenv (DROP n es)` by
    metis_tac[nonmutating_exprs_every, EVERY_DROP] >>
  `!n. ~exprs_can_mutate cenv (TAKE n (DROP 2 es))` by
    metis_tac[nonmutating_exprs_every, EVERY_TAKE] >>
  `!n. ~exprs_can_mutate cenv (DROP n (DROP 2 es))` by
    metis_tac[nonmutating_exprs_every, EVERY_DROP] >>
  Cases_on `kind` >> gvs[] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac check_create_blueprint_result_state >>
  imp_res_tac read_results_state >>
  imp_res_tac eval_create_preserves_scopes_immutables >> gvs[] >>
  rpt (qpat_x_assum `!a b c d e f. _` drule >> simp[] >> strip_tac) >>
  rpt (qpat_x_assum `!a b c. _` drule >> simp[] >> strip_tac) >>
  metis_tac[]
QED
Resume nonmutating_scopes_mutual[exprs]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED
Resume nonmutating_scopes_mutual[results]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >> metis_tac[]
QED
Finalise nonmutating_scopes_mutual

Theorem not_mutate_expr_scopes:
  !cenv cx e s v s'.
    ~expr_can_mutate cenv e /\ eval_expr cx e s = (INL v, s') ==>
    s'.scopes = s.scopes
Proof
  metis_tac[nonmutating_scopes_mutual]
QED
