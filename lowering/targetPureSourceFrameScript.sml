Theory targetPureSourceFrame
Ancestors
  supportedTargets supportedExprs supportedExprTraverse exprOracleStorageInterfaces
  vyperInterpreter vyperPureExpr
  vyperStatePreservation vyperPlaceFrames vyperCallFrame
  vyperState vyperContext vyperMisc
Libs
  monadsyntax

Theorem effect_free_source_mutual:
  (!cx:evaluation_context. !s:stmt. T) /\
  (!cx:evaluation_context. !ss:stmt list. T) /\
  (!cx:evaluation_context. !it:iterator. T) /\
  (!cx:evaluation_context. !tv:type_value. !id:string. !body:stmt list. !vs:eval_result list. T) /\
  (!cx e. !es result es'.
    ~supported_expr_exists expr_effect_root e /\ eval_expr cx e es = (result,es') ==>
    es' with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
    es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) /\
  (!cx args. !es result es'.
    ~supported_exprs_exists expr_effect_root args /\ eval_exprs cx args es = (result,es') ==>
    es' with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
    es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) /\
  (!cx:evaluation_context. !bt:base_assignment_target. T) /\
  (!cx:evaluation_context. !bt:base_assignment_target. T) /\
  (!cx:evaluation_context. !g:assignment_target. !v:value. T) /\
  (!cx:evaluation_context. !gs:assignment_target list. !vs:value list. T) /\
  (!cx args. !es result es'.
    ~supported_exprs_exists expr_effect_root args /\ eval_expr_results cx args es = (result,es') ==>
    es' with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
    es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[supported_expr_exists_def, expr_effect_root_def]
  >- (simp[evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
           type_check_def, assert_def, return_def] >>
      rpt strip_tac >> Cases_on `IS_SOME (lookup_scopes id es.scopes)` >>
      gvs[return_def, raise_def])
  >- (rpt strip_tac >> gvs[evaluate_def] >> drule lookup_global_state >> simp[evaluation_state_component_equality])
  >- (rpt strip_tac >> gvs[evaluate_def] >> drule lookup_flag_mem_state >> simp[])
  >- suspend "ifexp"
  >- (simp[evaluate_def, return_def])
  >- suspend "structlit"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "builtin"
  >- suspend "typebuiltin"
  >- (simp[evaluate_def, return_def])
  >- suspend "exprs_cons"
  >- (simp[evaluate_def, return_def])
  >> suspend "results_cons"
QED

Resume effect_free_source_mutual[ifexp]:
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), switch_BoolV_def, raise_def] >>
  imp_res_tac read_result_state >>
  imp_res_tac conditional_result_state >> gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[raise_def]) >>
  rpt (qpat_x_assum `!a b c. _` (drule_then assume_tac)) >> metis_tac[]
QED

Resume effect_free_source_mutual[structlit]:
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def,
      supported_fields_exists_not_every, supported_exprs_exists_not_every] >>
  first_x_assum drule >> simp[]
QED
Resume effect_free_source_mutual[subscript]:
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs()] >>
  rpt (qpat_x_assum `!s res t s' res' t'. _` drule_all >> strip_tac) >>
  Cases_on `subscript_reads_base cx e e'` >>
  gvs[bind_def, return_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >> gvs[] >>
  rpt (qpat_x_assum `!a b c. _` (drule_then assume_tac)) >>
  gvs[evaluation_state_component_equality]
QED
Resume effect_free_source_mutual[attribute]:
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs()] >>
  imp_res_tac select_result_state >> gvs[] >>
  first_x_assum (drule_then assume_tac) >>
  gvs[evaluation_state_component_equality]
QED
Resume effect_free_source_mutual[builtin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `bt = Len` >- suspend "builtin_len" >>
  Cases_on `bt = Bop In \/ bt = Bop NotIn` >- suspend "builtin_membership" >>
  Cases_on `bt = Env MsgGas` >- suspend "builtin_gas" >>
  suspend "builtin_ordinary"
QED
Resume effect_free_source_mutual[typebuiltin]:
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), ignore_bind_def,
      check_def, type_check_def, assert_def, return_def, raise_def, lift_sum_def] >>
  gvs[sum_CASE_rator, AllCaseEqs(), return_def, raise_def, ETA_THM] >> metis_tac[]
QED
Resume effect_free_source_mutual[exprs_cons]:
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >>
  qpat_x_assum `!a b c d f g. _` (drule_all_then assume_tac) >>
  rpt (qpat_x_assum `!a b c. _` (drule_then assume_tac)) >> metis_tac[]
QED
Resume effect_free_source_mutual[results_cons]:
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  rpt (qpat_x_assum `!a b c. _` (drule_then assume_tac)) >> metis_tac[]
QED

Resume effect_free_source_mutual[builtin_len]:
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def,
       type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[return_def] >>
  imp_res_tac result_array_length_state >> gvs[] >>
  `~supported_expr_exists expr_effect_root (HD args)` by
    (Cases_on `args` >> gvs[vyperContextTheory.builtin_args_length_ok_def, supported_expr_exists_def]) >>
  gvs[type_check_def, assert_def, return_def] >>
  rpt (qpat_x_assum `!a b c. _` (drule_then assume_tac)) >> metis_tac[]
QED
Resume effect_free_source_mutual[builtin_membership]:
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def,
       type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[type_check_def, assert_def, return_def] >>
  imp_res_tac lift_option_type_state >> imp_res_tac lift_sum_state >> gvs[] >>
  rpt (qpat_x_assum `!a b c. _` (drule_then assume_tac)) >> metis_tac[]
QED
Resume effect_free_source_mutual[builtin_gas]:
  rpt strip_tac >> gvs[] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac next_gas_reading_state >> gvs[]
QED
Resume effect_free_source_mutual[builtin_ordinary]:
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  Cases_on `builtin_args_length_ok bt (LENGTH args)` >>
  gvs[type_check_def, assert_def, return_def, raise_def, ignore_bind_def, bind_def] >>
  simp[AllCaseEqs(), return_def] >> strip_tac >> gvs[return_def] >>
  imp_res_tac get_accounts_state >> imp_res_tac lift_sum_state >>
  imp_res_tac precompile_call_success_state >> gvs[] >>
  drule_at (Pos last) builtin_operands_preserve >>
  disch_then (qspec_then
    `\a b. b with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
           a with <|gas_obs := []; outcomes := NONE; storage_trace := []|>` mp_tac) >>
  simp[] >>
  (impl_tac >- (rpt conj_tac >> rpt strip_tac >>
    gvs[code_slice_source_SOME, supported_expr_exists_def, expr_effect_root_def] >>
    metis_tac[])) >>
  simp[evaluation_state_component_equality]
QED

Finalise effect_free_source_mutual[local]


(* Effects exclude calls and Pop, not gas readings or precompile outcomes.
   Clearing only the observational fields therefore gives the frame needed
   for captured raw results, including local places. *)
Theorem effect_free_source_projection:
  !cx e es result es'.
    ~expr_has_effect e /\ eval_expr cx e es = (result,es') ==>
    es' with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
    es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>
Proof
  rpt strip_tac >> irule (cj 5 effect_free_source_mutual) >>
  gvs[expr_has_effect_def] >> metis_tac[]
QED


Theorem target_pure_source_mutual:
  (!tops e. supported_pure_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==>
      s' with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
      s with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) /\
  (!tops es. supported_pure_exprs tops es ==>
    (!cx s r s'. eval_exprs cx es s = (r,s') ==>
      s' with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
      s with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) /\
    (!e. MEM e es ==> !cx s r s'. eval_expr cx e s = (r,s') ==>
      s' with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
      s with <|gas_obs := []; outcomes := NONE; storage_trace := []|>)) /\
  (!tops fields. supported_pure_fields tops fields ==>
    !cx s r s'. eval_exprs cx (MAP SND fields) s = (r,s') ==>
      s' with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
      s with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) /\
  (!tops e. supported_place_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==>
      s' with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
      s with <|gas_obs := []; outcomes := NONE; storage_trace := []|>)
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rpt strip_tac >>
  imp_res_tac supported_pure_no_effect >>
  fs[supported_exprs_exists_not_every, supported_fields_exists_not_every,
     listTheory.EVERY_MEM]
  >>~- ([`eval_exprs cx args es = (result,es')`],
      drule_at (Pat `eval_exprs _ _ _ = _`)
        (cj 6 effect_free_source_mutual) >>
      simp[supported_exprs_exists_not_every, listTheory.EVERY_MEM]) >>
  drule_at (Pat `eval_expr _ _ _ = _`) (cj 5 effect_free_source_mutual) >>
  simp[]
QED

Theorem target_pure_base_source_projection:
  !bt tops cx s r s'.
    supported_target_pure tops bt /\
    eval_base_place cx bt s = (r,s') ==>
      s' with <|gas_obs := []; outcomes := NONE; storage_trace := []|> =
      s with <|gas_obs := []; outcomes := NONE; storage_trace := []|>
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac
  >~ [`TopLevelNameTarget p`]
  >- (PairCases_on `p` >> simp[supported_target_pure_def, Once evaluate_def] >>
      rpt strip_tac >> drule lookup_global_state >> strip_tac >>
      gvs[evaluation_state_component_equality]) >>
  simp[supported_target_pure_def, Once evaluate_def] >> rpt strip_tac
  >- (gvs[bind_def, get_scopes_def, type_check_def, assert_def,
          ignore_bind_def, return_def, raise_def, AllCaseEqs()]) >>
  gvs[bind_def, AllCaseEqs()] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[vyperASTTheory.expr_size_def] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
  gvs[raise_def] >>
  first_x_assum (drule_all_then assume_tac) >>
  gvs[evaluation_state_component_equality] >>
  drule (cj 1 target_pure_source_mutual) >>
  disch_then drule >> simp[evaluation_state_component_equality]
QED

Theorem target_pure_base_source_frame:
  supported_target_pure tops bt /\ eval_base_place cx bt s = (r,s') ==>
  ?gs os st. s' = s with <|gas_obs := gs; outcomes := os; storage_trace := st|>
Proof
  strip_tac >> drule_all target_pure_base_source_projection >>
  simp[evaluation_state_component_equality] >> fs[evaluation_state_component_equality] >> metis_tac[]
QED
