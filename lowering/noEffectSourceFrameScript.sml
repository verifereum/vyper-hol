Theory noEffectSourceFrame
Ancestors
  supportedExprTraverse vyperInterpreter vyperStatePreservation vyperPlaceFrames
  vyperStorageBackend vyperState vyperContext vyperMisc pair sum

Theorem no_effect_source_frame_mutual[local]:
  (!(p:expr->bool) e. ~supported_expr_exists expr_effect_root e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==>
      s'.scopes = s.scopes /\ s'.immutables = s.immutables /\
      (!tr. get_storage cx s' tr = get_storage cx s tr)) /\
  (!(p:expr->bool) (target:base_assignment_target). T) /\
  (!(p:expr->bool) es. ~supported_exprs_exists expr_effect_root es ==>
    (!cx s r s'. eval_exprs cx es s = (r,s') ==>
      s'.scopes = s.scopes /\ s'.immutables = s.immutables /\
      (!tr. get_storage cx s' tr = get_storage cx s tr)) /\
    (!e. MEM e es ==> !cx s r s'. eval_expr cx e s = (r,s') ==>
      s'.scopes = s.scopes /\ s'.immutables = s.immutables /\
      (!tr. get_storage cx s' tr = get_storage cx s tr))) /\
  (!(p:expr->bool) (opt:expr option). T) /\
  (!(p:expr->bool) fields. ~supported_fields_exists expr_effect_root fields ==>
    !cx s r s'. eval_exprs cx (MAP SND fields) s = (r,s') ==>
      s'.scopes = s.scopes /\ s'.immutables = s.immutables /\
      (!tr. get_storage cx s' tr = get_storage cx s tr))
Proof
  ho_match_mp_tac supported_expr_exists_ind >>
  simp[supported_expr_exists_def, expr_effect_root_def] >>
  rpt conj_tac >> rpt gen_tac
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()])
  >- simp[Once evaluate_def, return_def]
  >- suspend "global"
  >- suspend "flag"
  >- suspend "ifexp"
  >- suspend "struct"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "builtin"
  >- suspend "typebuiltin"
  >- simp[Once evaluate_def, return_def]
  >- suspend "cons"
  >- simp[Once evaluate_def, return_def]
  >> suspend "fields"
QED

Resume no_effect_source_frame_mutual[global]:
  PairCases_on `id` >> rpt strip_tac >>
  gvs[Once evaluate_def] >> imp_res_tac lookup_global_state >> gvs[]
QED
Resume no_effect_source_frame_mutual[flag]:
  PairCases_on `id` >> rpt strip_tac >>
  gvs[Once evaluate_def, lookup_flag_mem_def, option_CASE_rator,
      AllCaseEqs(), return_def, raise_def]
QED
Resume no_effect_source_frame_mutual[ifexp]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs(),
      return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac conditional_result_state >>
  gvs[] >> gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED
Resume no_effect_source_frame_mutual[struct]:
  PairCases_on `id` >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >> metis_tac[]
QED
Resume no_effect_source_frame_mutual[subscript]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED
Resume no_effect_source_frame_mutual[attribute]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Resume no_effect_source_frame_mutual[builtin]:
  ntac 2 strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  rpt gen_tac >> disch_tac >>
  Cases_on `blt = Len`
  >- (gvs[Once evaluate_def, builtin_args_length_ok_def, bind_def,
          ignore_bind_def, type_check_def, assert_def, return_def,
          raise_def, AllCaseEqs()] >>
      imp_res_tac result_array_length_state >> gvs[] >>
      `MEM (HD es) es` by
        (Cases_on `es` >> gvs[builtin_args_length_ok_def]) >>
      metis_tac[]) >>
  Cases_on `blt = Env MsgGas` >> gvs[] >>
  Cases_on `blt = Bop In \/ blt = Bop NotIn` >> gvs[] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, COND_RATOR, lift_option_type_def,
      option_CASE_rator, AllCaseEqs()] >>
  imp_res_tac result_array_length_state >>
  imp_res_tac lift_option_type_state >>
  imp_res_tac next_gas_reading_state >>
  imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >>
  imp_res_tac precompile_call_success_state >>
  gvs[boolTheory.FORALL_BOOL, get_storage_def] >> metis_tac[]
QED
Resume no_effect_source_frame_mutual[typebuiltin]:
  rpt strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED
Resume no_effect_source_frame_mutual[cons]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED
Resume no_effect_source_frame_mutual[fields]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED
Finalise no_effect_source_frame_mutual

Theorem no_effect_eval_expr_frame:
  ~expr_has_effect e /\ eval_expr cx e s = (r,s') ==>
  s'.scopes = s.scopes /\ s'.immutables = s.immutables /\
  (!tr. get_storage cx s' tr = get_storage cx s tr)
Proof
  simp[expr_has_effect_def] >>
  metis_tac[no_effect_source_frame_mutual]
QED

Theorem no_effect_eval_exprs_frame:
  EVERY (\e. ~expr_has_effect e) es /\
  eval_exprs cx es s = (r,s') ==>
  s'.scopes = s.scopes /\ s'.immutables = s.immutables /\
  (!tr. get_storage cx s' tr = get_storage cx s tr)
Proof
  pure_rewrite_tac[listTheory.EVERY_NOT_EXISTS, expr_has_effect_def] >>
  BETA_TAC >>
  simp_tac (bool_ss ++ ETA_ss) [GSYM supported_exprs_exists_every] >>
  metis_tac[no_effect_source_frame_mutual]
QED

Theorem no_effect_eval_results_frame:
  EVERY (\e. ~expr_has_effect e) es /\
  eval_expr_results cx es s = (r,s') ==>
  s'.scopes = s.scopes /\ s'.immutables = s.immutables /\
  (!tr. get_storage cx s' tr = get_storage cx s tr)
Proof
  qid_spec_tac `s` >> qid_spec_tac `r` >> qid_spec_tac `s'` >>
  Induct_on `es` >>
  simp[Once evaluate_def, return_def] >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  imp_res_tac no_effect_eval_expr_frame >> metis_tac[]
QED
