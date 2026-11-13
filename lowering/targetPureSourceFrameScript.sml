Theory targetPureSourceFrame
Ancestors
  supportedTargets supportedExprs vyperInterpreter vyperPureExpr
  vyperStatePreservation vyperPlaceFrames vyperCallFrame
  vyperState vyperContext vyperMisc targetPlaceSimCasesBase
Libs
  monadsyntax

Theorem target_pure_source_mutual:
  (!tops e. supported_pure_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==>
      s' with <|gas_obs := []; outcomes := NONE|> =
      s with <|gas_obs := []; outcomes := NONE|>) /\
  (!tops es. supported_pure_exprs tops es ==>
    (!cx s r s'. eval_exprs cx es s = (r,s') ==>
      s' with <|gas_obs := []; outcomes := NONE|> =
      s with <|gas_obs := []; outcomes := NONE|>) /\
    (!e. MEM e es ==> !cx s r s'. eval_expr cx e s = (r,s') ==>
      s' with <|gas_obs := []; outcomes := NONE|> =
      s with <|gas_obs := []; outcomes := NONE|>)) /\
  (!tops fields. supported_pure_fields tops fields ==>
    !cx s r s'. eval_exprs cx (MAP SND fields) s = (r,s') ==>
      s' with <|gas_obs := []; outcomes := NONE|> =
      s with <|gas_obs := []; outcomes := NONE|>) /\
  (!tops e. supported_place_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==>
      s' with <|gas_obs := []; outcomes := NONE|> =
      s with <|gas_obs := []; outcomes := NONE|>)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[supported_pure_expr_def]
  >- (metis_tac[eval_expr_preserves_state, pure_expr_def])
  >- simp[Once evaluate_def, return_def]
  >- (metis_tac[eval_expr_preserves_state, pure_expr_def])
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
  >- (metis_tac[eval_expr_preserves_state, pure_expr_def])
  >- (metis_tac[eval_expr_preserves_state, pure_expr_def])
  >- suspend "place_subscript"
  >> suspend "place_rest"
QED

Resume target_pure_source_mutual[ifexp]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs(),
      return_def, raise_def] >>
  imp_res_tac read_result_state >>
  imp_res_tac conditional_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED
Resume target_pure_source_mutual[structlit]:
  PairCases_on `id` >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >> metis_tac[]
QED
Resume target_pure_source_mutual[subscript]:
  rpt strip_tac >> Cases_on `subscript_reads_base cx e e'` >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED
Resume target_pure_source_mutual[attribute]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Resume target_pure_source_mutual[builtin]:
  rpt strip_tac >>
  `code_slice_source blt es = NONE` by
    (Cases_on `code_slice_source blt es` >> simp[] >>
     rename1 `SOME p` >> PairCases_on `p` >>
     gvs[code_slice_source_SOME,
         supportedExprFormsTheory.supported_builtin_form_def]) >>
  Cases_on `blt = Len` >> Cases_on `blt = Env MsgGas` >>
  Cases_on `blt = Bop In \/ blt = Bop NotIn` >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, COND_RATOR,
      vfmTypesTheory.option_CASE_rator, AllCaseEqs()] >>
  imp_res_tac result_array_length_state >>
  imp_res_tac lift_option_type_state >> imp_res_tac lift_sum_state >>
  gvs[next_gas_reading_def, precompile_call_success_def,
      check_def, assert_def, bind_def, return_def, raise_def, get_accounts_def, lift_sum_def,
      AllCaseEqs()] >>
  gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
  Cases_on `es` >> gvs[builtin_args_length_ok_def] >>
  metis_tac[]
QED
Resume target_pure_source_mutual[typebuiltin]:
  rpt strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED
Resume target_pure_source_mutual[nil]:
  simp[Once evaluate_def, return_def]
QED
Resume target_pure_source_mutual[cons]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED
Resume target_pure_source_mutual[fields_nil]:
  simp[Once evaluate_def, return_def]
QED
Resume target_pure_source_mutual[fields_cons]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED
Resume target_pure_source_mutual[place_subscript]:
  rpt strip_tac >> Cases_on `subscript_reads_base cx e e'` >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED
Resume target_pure_source_mutual[place_rest]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Finalise target_pure_source_mutual

Theorem target_pure_base_source_projection:
  !bt tops cx s r s'.
    supported_target_pure tops bt /\
    eval_base_place cx bt s = (r,s') ==>
      s' with <|gas_obs := []; outcomes := NONE|> =
      s with <|gas_obs := []; outcomes := NONE|>
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac
  >~ [`TopLevelNameTarget p`]
  >- (PairCases_on `p` >> simp[supported_target_pure_def, Once evaluate_def] >>
      rpt strip_tac >> metis_tac[lookup_global_state]) >>
  simp[supported_target_pure_def, Once evaluate_def] >> rpt strip_tac
  >- (gvs[bind_def, get_scopes_def, type_check_def, assert_def,
          ignore_bind_def, return_def, raise_def, AllCaseEqs()]) >>
  gvs[bind_def, AllCaseEqs()] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[vyperASTTheory.expr_size_def] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
  gvs[raise_def] >>
  first_x_assum (drule_all_then assume_tac) >>
  gvs[] >>
  drule (cj 1 target_pure_source_mutual) >>
  disch_then drule >> simp[]
QED

Theorem target_pure_base_source_frame:
  supported_target_pure tops bt /\ eval_base_place cx bt s = (r,s') ==>
  ?gs os. s' = s with <|gas_obs := gs; outcomes := os|>
Proof
  strip_tac >> drule_all target_pure_base_source_projection >>
  simp[evaluation_state_component_equality] >> metis_tac[]
QED
