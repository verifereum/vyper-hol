Theory bodySimAugPlaceScopes
Ancestors
  supportedExprs vyperInterpreter vyperScopePreservation
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
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac result_array_length_state >>
  imp_res_tac next_gas_reading_state >>
  imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >> gvs[] >>
  gvs[builtin_args_length_ok_def] >>
  Cases_on `es` >> gvs[] >> metis_tac[]
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
