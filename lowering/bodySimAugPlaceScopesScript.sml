Theory bodySimAugPlaceScopes
Ancestors
  supportedExprs vyperInterpreter vyperCallOutcomeFrame vyperScopePreservation
  vyperState vyperContext vyperMisc pair sum
  vyperStatePreservation vyperPlaceFrames vyperCallFrame

Theorem aug_place_pure_scopes_mutual:
  (!tops e. supported_pure_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==> s'.scopes = s.scopes) /\
  (!tops es. supported_pure_exprs tops es ==>
    (!cx s r s'. eval_exprs cx es s = (r,s') ==> s'.scopes = s.scopes) /\
    (!e. MEM e es ==> !cx s r s'.
      eval_expr cx e s = (r,s') ==> s'.scopes = s.scopes)) /\
  (!tops fields. supported_pure_fields tops fields ==>
    !cx s r s'. eval_exprs cx (MAP SND fields) s = (r,s') ==> s'.scopes = s.scopes) /\
  (!tops e. supported_place_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==> s'.scopes = s.scopes)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[supported_pure_expr_def]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()])
  >- simp[Once evaluate_def, return_def]
  >- (PairCases_on `id` >> rpt strip_tac >>
      gvs[Once evaluate_def] >> metis_tac[lookup_global_scopes])
  >- suspend "ifexp"
  >- suspend "structlit"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "builtin"
  >- suspend "typebuiltin"
  >- suspend "nil"
  >- suspend "cons"
  >- suspend "fields_nil"
  >- suspend "fields_cons"
  >- suspend "place_name"
  >- suspend "place_global"
  >- suspend "place_subscript"
  >> suspend "place_rest"
QED

Resume aug_place_pure_scopes_mutual[ifexp]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs(),
      return_def, raise_def] >>
  imp_res_tac read_result_state >>
  imp_res_tac conditional_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED
Resume aug_place_pure_scopes_mutual[structlit]:
  PairCases_on `id` >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >> metis_tac[]
QED
Resume aug_place_pure_scopes_mutual[subscript]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED
Resume aug_place_pure_scopes_mutual[attribute]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Resume aug_place_pure_scopes_mutual[builtin]:
  rpt strip_tac >>
  Cases_on `blt = Len` >> Cases_on `blt = Env MsgGas` >>
  Cases_on `blt = Bop In \/ blt = Bop NotIn` >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, COND_RATOR, lift_option_type_def,
      vfmTypesTheory.option_CASE_rator,
      AllCaseEqs()] >>
  imp_res_tac result_array_length_state >>
  imp_res_tac lift_option_type_state >>
  imp_res_tac next_gas_reading_state >>
  imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >>
  imp_res_tac precompile_call_success_state >> gvs[] >>
  gvs[builtin_args_length_ok_def] >>
  Cases_on `es` >> gvs[] >> res_tac >> gvs[]
QED
Resume aug_place_pure_scopes_mutual[typebuiltin]:
  rpt strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED
Resume aug_place_pure_scopes_mutual[nil]:
  simp[Once evaluate_def, return_def]
QED
Resume aug_place_pure_scopes_mutual[cons]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED
Resume aug_place_pure_scopes_mutual[fields_nil]:
  simp[Once evaluate_def, return_def]
QED
Resume aug_place_pure_scopes_mutual[fields_cons]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED
Resume aug_place_pure_scopes_mutual[place_name]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
QED
Resume aug_place_pure_scopes_mutual[place_global]:
  PairCases_on `id` >> rpt strip_tac >>
  gvs[Once evaluate_def] >> metis_tac[lookup_global_scopes]
QED
Resume aug_place_pure_scopes_mutual[place_subscript]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED
Resume aug_place_pure_scopes_mutual[place_rest]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Finalise aug_place_pure_scopes_mutual

Theorem aug_place_pure_expr_scopes:
  supported_pure_expr tops e /\ eval_expr cx e s = (r,s') ==>
  s'.scopes = s.scopes
Proof
  metis_tac[aug_place_pure_scopes_mutual]
QED

Theorem aug_place_place_expr_scopes:
  supported_place_expr tops e /\ eval_expr cx e s = (r,s') ==>
  s'.scopes = s.scopes
Proof
  metis_tac[aug_place_pure_scopes_mutual]
QED

Theorem aug_place_pure_exprs_scopes:
  supported_pure_exprs tops es /\ eval_exprs cx es s = (r,s') ==>
  s'.scopes = s.scopes
Proof
  metis_tac[aug_place_pure_scopes_mutual]
QED

Theorem aug_place_pure_results_scopes:
  !es tops cx s r s'. supported_pure_exprs tops es /\
    eval_expr_results cx es s = (r,s') ==> s'.scopes = s.scopes
Proof
  Induct >> simp[supported_pure_expr_def, Once evaluate_def, return_def] >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs(), return_def] >>
  metis_tac[aug_place_pure_expr_scopes]
QED


Theorem aug_place_lookup_global_not_memory:
  lookup_global cx src id s = (INL pv,s') ==>
  !name path. pv <> PlaceR (MemoryPlace name path)
Proof
  Cases_on `get_module_code cx src`
  >- simp[lookup_global_def, lift_option_type_def, bind_def, raise_def] >>
  Cases_on `find_var_decl_by_name id x`
  >- (simp[lookup_global_def, lift_option_type_def, bind_def,
           return_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  PairCases_on `x'` >> Cases_on `x'0` >>
  simp[lookup_global_def, lift_option_type_def, bind_def,
       return_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[option_CASE_rator, return_def, raise_def, AllCaseEqs()]
QED

Theorem aug_place_top_level_pop_scopes:
  eval_expr cx (Pop ty (TopLevelNameTarget id)) s = (r,s') ==>
  s'.scopes = s.scopes
Proof
  PairCases_on `id` >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac lookup_global_state >> imp_res_tac get_place_state >> gvs[] >>
  imp_res_tac aug_place_lookup_global_not_memory >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  Cases_on `p` >> gvs[] >>
  imp_res_tac pop_storage_place_scopes_immutables >>
  gvs[pop_place_def, raise_def] >>
  gvs[bind_def, ignore_bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac get_immutables_scopes >>
  imp_res_tac lift_option_type_scopes >>
  imp_res_tac lift_sum_scopes >>
  imp_res_tac set_immutable_scopes >> gvs[]
QED

Theorem aug_place_lock_scopes[local]:
  lock_if_nr cx nr is_view s = (r,s') ==> s'.scopes = s.scopes
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[raise_def] >>
  simp[ignore_bind_def, bind_def, AllCaseEqs(), check_not_static_def,
       check_def, assert_def, return_def, raise_def] >>
  rw[] >> imp_res_tac acquire_nonreentrant_lock_scopes >>
  gvs[return_def, vyperStateTheory.assert_def]
QED

Theorem aug_place_unlock_scopes[local]:
  unlock_if_nr cx nr is_view s = (r,s') ==> s'.scopes = s.scopes
Proof
  Cases_on `nr /\ ~is_view` >> simp[unlock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[return_def] >>
  metis_tac[release_nonreentrant_lock_scopes]
QED

Theorem aug_place_finally_call_scopes[local]:
  finally_unless_halt (finally f (pop_function prev))
    (unlock_if_nr cx nr is_view) s = (r,s') ==> s'.scopes = prev
Proof
  qabbrev_tac `g = unlock_if_nr cx nr is_view` >>
  `!t r t'. g t = (r,t') ==> t'.scopes = t.scopes`
    by metis_tac[aug_place_unlock_scopes, markerTheory.Abbrev_def] >>
  strip_tac >>
  Cases_on `finally f (pop_function prev) s` >> rename1 `_ = (q0,s0)` >>
  `s0.scopes = prev` by
    (qpat_x_assum `finally _ _ _ = _` mp_tac >>
     simp[finally_def, pop_function_def, set_scopes_def, bind_def,
          ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
     rw[] >> gvs[]) >>
  qpat_x_assum `finally_unless_halt _ _ _ = _` mp_tac >>
  simp[finally_unless_halt_def] >>
  Cases_on `q0` >> TRY (Cases_on `y`) >>
  simp[ignore_bind_def, bind_def, return_def, raise_def] >>
  Cases_on `g s0` >> rename1 `g s0 = (gr,gs)` >> Cases_on `gr` >>
  simp[] >> rw[] >> res_tac >> gvs[]
QED

Theorem aug_place_intcall_scopes:
  (!s0 r0 s1. eval_expr_results cx es s0 = (r0,s1) ==>
    s1.scopes = s0.scopes) /\
  eval_expr cx (Call ty (IntCall id) es kw) s = (r,s') ==>
  s'.scopes = s.scopes
Proof
  PairCases_on `id` >> strip_tac >>
  Cases_on `MEM (id0,id1) cx.stk`
  >- gvs[Once evaluate_def, type_check_def, assert_def, ignore_bind_def,
         bind_def, raise_def] >>
  Cases_on `get_module_code cx id0`
  >- gvs[Once evaluate_def, type_check_def, assert_def, ignore_bind_def,
         bind_def, lift_option_type_def, return_def, raise_def] >>
  Cases_on `lookup_callable_function cx.in_deploy id1 x`
  >- gvs[Once evaluate_def, type_check_def, assert_def, ignore_bind_def,
         bind_def, lift_option_type_def, return_def, raise_def] >>
  PairCases_on `x'` >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, lift_option_type_def,
      return_def, raise_def, get_scopes_def, AllCaseEqs()] >>
  rule_assum_tac (PURE_REWRITE_RULE
    [GSYM (SRULE [] unlock_if_nr_def), GSYM lock_if_nr_def]) >>
  imp_res_tac finally_set_scopes >>
  imp_res_tac aug_place_finally_call_scopes >>
  imp_res_tac read_results_state >>
  imp_res_tac aug_place_lock_scopes >>
  imp_res_tac (REWRITE_RULE [lock_if_nr_def, ignore_bind_def] aug_place_lock_scopes) >>
  gvs[option_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
  first_x_assum drule >> strip_tac >> gvs[push_function_def, return_def] >>
  imp_res_tac (GEN_ALL (SRULE [unlock_if_nr_def]
    (Q.INST [`is_view` |-> `mut = View \/ mut = Pure`]
       aug_place_finally_call_scopes))) >> gvs[]
QED

Theorem aug_place_effect_scopes_mutual:
  (!tops e. supported_effect_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==> s'.scopes = s.scopes) /\
  (!tops e. supported_effect_place_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==> s'.scopes = s.scopes)
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> simp[supported_effect_expr_def]
  >- suspend "intcall"
  >- suspend "extcall"
  >- suspend "send"
  >- suspend "send_gas"
  >- suspend "pop"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "place_subscript"
  >> suspend "place_attribute"
QED

Resume aug_place_effect_scopes_mutual[subscript]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[aug_place_pure_expr_scopes, aug_place_place_expr_scopes]
QED
Resume aug_place_effect_scopes_mutual[attribute]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Resume aug_place_effect_scopes_mutual[place_subscript]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[aug_place_pure_expr_scopes, aug_place_place_expr_scopes]
QED
Resume aug_place_effect_scopes_mutual[place_attribute]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Resume aug_place_effect_scopes_mutual[send]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac eval_send_preserves_non_accounts >> gvs[] >>
  metis_tac[aug_place_pure_exprs_scopes, supported_pure_expr_def]
QED
Resume aug_place_effect_scopes_mutual[send_gas]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac eval_send_preserves_non_accounts >> gvs[] >>
  metis_tac[aug_place_pure_exprs_scopes, supported_pure_expr_def]
QED
Resume aug_place_effect_scopes_mutual[extcall]:
  rpt strip_tac >>
  `supported_pure_exprs tops (TAKE 1 args) /\
   supported_pure_exprs tops (TAKE (LENGTH arg_types) (DROP 1 args)) /\
   supported_pure_exprs tops (DROP (1 + LENGTH arg_types) args)` by
    (gvs[supported_pure_exprs_every] >>
     metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac eval_ext_call_preserves_non_accounts >>
  imp_res_tac read_results_state >> gvs[] >>
  metis_tac[aug_place_pure_exprs_scopes, aug_place_pure_results_scopes]
QED
Resume aug_place_effect_scopes_mutual[pop]:
  rpt strip_tac >> irule aug_place_top_level_pop_scopes >>
  goal_assum (drule_at Any)
QED
Resume aug_place_effect_scopes_mutual[intcall]:
  rpt strip_tac >> irule aug_place_intcall_scopes >>
  goal_assum (drule_at Any) >>
  metis_tac[aug_place_pure_results_scopes]
QED
Finalise aug_place_effect_scopes_mutual

Theorem aug_place_supported_expr_scopes:
  supported_expr tops e /\ eval_expr cx e s = (r,s') ==>
  s'.scopes = s.scopes
Proof
  simp[supported_expr_def] >>
  metis_tac[aug_place_pure_expr_scopes, aug_place_effect_scopes_mutual]
QED
