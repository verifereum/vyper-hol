Theory bodySimAugPlaceScopes
Ancestors
  targetPureSourceFrame
  supportedExprs vyperInterpreter vyperCallOutcomeFrame vyperScopePreservation
  vyperState vyperContext vyperMisc pair sum
  vyperStatePreservation vyperPlaceFrames vyperCallFrame vyperLocalAccessFrame

(* select_result and lookup_global now append to the storage trace: read
   the scopes equation off the result state's trace-update form. *)
val trace_scopes_tac =
  rpt (qpat_x_assum `_ = _ with storage_trace := _`
    (fn th => assume_tac (SIMP_RULE (srw_ss()) []
      (AP_TERM ``\s:evaluation_state. s.scopes`` th)))) >> gvs[];

Theorem aug_place_pure_scopes_mutual:
  (!tops e. supported_effect_free_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==> s'.scopes = s.scopes) /\
  (!tops es. supported_effect_free_exprs tops es ==>
    (!cx s r s'. eval_exprs cx es s = (r,s') ==> s'.scopes = s.scopes) /\
    (!e. MEM e es ==> !cx s r s'.
      eval_expr cx e s = (r,s') ==> s'.scopes = s.scopes)) /\
  (!tops fields. supported_effect_free_fields tops fields ==>
    !cx s r s'. eval_exprs cx (MAP SND fields) s = (r,s') ==> s'.scopes = s.scopes) /\
  (!tops e. supported_effect_free_place_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==> s'.scopes = s.scopes)
Proof
  rpt conj_tac >> rpt strip_tac >>
  imp_res_tac target_pure_source_mutual >>
  fs[evaluation_state_component_equality]
QED

Theorem aug_place_pure_expr_scopes:
  supported_effect_free_expr tops e /\ eval_expr cx e s = (r,s') ==>
  s'.scopes = s.scopes
Proof
  metis_tac[aug_place_pure_scopes_mutual]
QED

Theorem aug_place_place_expr_scopes:
  supported_effect_free_place_expr tops e /\ eval_expr cx e s = (r,s') ==>
  s'.scopes = s.scopes
Proof
  metis_tac[aug_place_pure_scopes_mutual]
QED

Theorem aug_place_pure_exprs_scopes:
  supported_effect_free_exprs tops es /\ eval_exprs cx es s = (r,s') ==>
  s'.scopes = s.scopes
Proof
  metis_tac[aug_place_pure_scopes_mutual]
QED

Theorem aug_place_top_level_pop_scopes:
  eval_expr cx (Pop ty (TopLevelNameTarget id)) s = (r,s') ==>
  s'.scopes = s.scopes
Proof
  PairCases_on `id` >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac lookup_global_state >> imp_res_tac get_place_state >>
  trace_scopes_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  Cases_on `p` >> gvs[lookup_global_not_memory] >>
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

Theorem aug_place_intcall_scopes:
  (!s0 r0 s1. eval_exprs cx es s0 = (r0,s1) ==>
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
  imp_res_tac call_cleanup_scopes >>
  imp_res_tac read_results_state >>
  imp_res_tac aug_place_lock_scopes >>
  imp_res_tac (REWRITE_RULE [lock_if_nr_def, ignore_bind_def] aug_place_lock_scopes) >>
  gvs[option_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
  first_x_assum drule >> strip_tac >> gvs[push_function_def, return_def] >>
  imp_res_tac (GEN_ALL (SRULE [unlock_if_nr_def]
    (Q.INST [`is_view` |-> `mut = View \/ mut = Pure`]
       call_cleanup_scopes))) >> gvs[]
QED

Theorem aug_place_effect_scopes_mutual:
  (!tops e. supported_root_effect_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==> s'.scopes = s.scopes) /\
  (!tops e. supported_root_effect_place_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==> s'.scopes = s.scopes)
Proof
  ho_match_mp_tac supported_root_effect_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> simp[supported_root_effect_expr_def]
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
  gvs[COND_RATOR, AllCaseEqs(), bind_def, return_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  trace_scopes_tac >> metis_tac[aug_place_pure_expr_scopes, aug_place_place_expr_scopes]
QED
Resume aug_place_effect_scopes_mutual[attribute]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> trace_scopes_tac >> metis_tac[]
QED
Resume aug_place_effect_scopes_mutual[place_subscript]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  gvs[COND_RATOR, AllCaseEqs(), bind_def, return_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  trace_scopes_tac >> metis_tac[aug_place_pure_expr_scopes, aug_place_place_expr_scopes]
QED
Resume aug_place_effect_scopes_mutual[place_attribute]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> trace_scopes_tac >> metis_tac[]
QED
Resume aug_place_effect_scopes_mutual[send]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, AllCaseEqs()] >>
  `supported_effect_free_exprs tops [a; v]` by simp[supported_effect_free_expr_def] >>
  imp_res_tac eval_send_preserves_non_accounts >>
  imp_res_tac aug_place_pure_exprs_scopes >> gvs[]
QED
Resume aug_place_effect_scopes_mutual[send_gas]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, AllCaseEqs()] >>
  `supported_effect_free_exprs tops [a; v; g]` by simp[supported_effect_free_expr_def] >>
  imp_res_tac eval_send_preserves_non_accounts >>
  imp_res_tac aug_place_pure_exprs_scopes >> gvs[]
QED
Resume aug_place_effect_scopes_mutual[extcall]:
  rpt strip_tac >>
  `supported_effect_free_exprs tops (TAKE 1 args) /\
   supported_effect_free_exprs tops (TAKE (LENGTH arg_types) (DROP 1 args)) /\
   supported_effect_free_exprs tops (DROP (1 + LENGTH arg_types) args)` by
    (gvs[supported_effect_free_exprs_every] >>
     metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac eval_ext_call_preserves_non_accounts >>
  imp_res_tac read_results_state >> gvs[] >>
  metis_tac[aug_place_pure_exprs_scopes]
QED
Resume aug_place_effect_scopes_mutual[pop]:
  rpt strip_tac >> irule aug_place_top_level_pop_scopes >>
  goal_assum (drule_at Any)
QED
Resume aug_place_effect_scopes_mutual[intcall]:
  rpt strip_tac >> irule aug_place_intcall_scopes >>
  goal_assum (drule_at Any) >>
  metis_tac[aug_place_pure_exprs_scopes]
QED
Finalise aug_place_effect_scopes_mutual

Theorem aug_place_supported_expr_scopes:
  supported_root_expr tops e /\ eval_expr cx e s = (r,s') ==>
  s'.scopes = s.scopes
Proof
  simp[supported_root_expr_def] >>
  metis_tac[aug_place_pure_expr_scopes, aug_place_effect_scopes_mutual]
QED
