Theory exprNoEffectStorage
Ancestors
  exprNoPopScopes vyperInterpreter supportedExprTraverse vyperState
  vyperStatePreservation vyperPlaceFrames vyperContext vyperStorageBackend

Theorem eval_mutual_noeffect_storage[local]:
  (!cx:evaluation_context. !s:stmt. T) /\
  (!cx:evaluation_context. !ss:stmt list. T) /\
  (!cx:evaluation_context. !it:iterator. T) /\
  (!cx:evaluation_context. !tv:type_value. !id:string. !body:stmt list. !vs:value list. T) /\
  (!cx e st res st'. ~expr_has_effect e /\ eval_expr cx e st = (res,st') ==>
    !tr. get_storage cx st' tr = get_storage cx st tr) /\
  (!cx es st res st'. ~supported_exprs_exists expr_effect_root es /\
    eval_exprs cx es st = (res,st') ==> !tr. get_storage cx st' tr = get_storage cx st tr) /\
  (!cx bt st res st'. ~supported_target_exists expr_effect_root bt /\
    eval_base_place cx bt st = (res,st') ==> !tr. get_storage cx st' tr = get_storage cx st tr) /\
  (!cx bt st res st'. ~supported_target_exists expr_effect_root bt /\
    eval_target_place cx bt st = (res,st') ==> !tr. get_storage cx st' tr = get_storage cx st tr) /\
  (!cx:evaluation_context. !g:assignment_target. !v:value. T) /\
  (!cx:evaluation_context. !gs:assignment_target list. !vs:value list. T) /\
  (!cx es st res st'. ~supported_exprs_exists expr_effect_root es /\
    eval_expr_results cx es st = (res,st') ==> !tr. get_storage cx st' tr = get_storage cx st tr)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def]
  >- suspend "Name"
  >- suspend "TopLevel"
  >- suspend "Flag"
  >- suspend "IfExp"
  >- suspend "Literal"
  >- suspend "StructLit"
  >- suspend "Subscript"
  >- suspend "Attribute"
  >- suspend "Builtin"
  >- suspend "TypeBuiltin"
  >- suspend "ExprsNil"
  >- suspend "ExprsCons"
  >- suspend "BaseName"
  >- suspend "BaseTopLevel"
  >- suspend "BaseAttribute"
  >- suspend "BaseSubscript"
  >- suspend "Target"
  >- suspend "ResultsNil"
  >> suspend "ResultsCons"
QED

Resume eval_mutual_noeffect_storage[Name]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, lift_option_type_def,
      return_def, raise_def, AllCaseEqs()]
QED

Resume eval_mutual_noeffect_storage[TopLevel]:
  rpt strip_tac >> gvs[Once evaluate_def] >>
  drule lookup_global_state >> simp[]
QED

Resume eval_mutual_noeffect_storage[Flag]:
  rpt strip_tac >> gvs[Once evaluate_def] >>
  drule lookup_flag_mem_state >> simp[]
QED

Resume eval_mutual_noeffect_storage[IfExp]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def,
      switch_BoolV_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >>
  imp_res_tac conditional_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED

Resume eval_mutual_noeffect_storage[Literal]:
  simp[Once evaluate_def, return_def]
QED

Resume eval_mutual_noeffect_storage[StructLit]:
  rpt strip_tac >>
  gvs[supported_fields_exists_every, supported_exprs_exists_every,
      listTheory.EXISTS_MAP, Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  metis_tac[]
QED

Resume eval_mutual_noeffect_storage[Subscript]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED

Resume eval_mutual_noeffect_storage[Attribute]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED

Resume eval_mutual_noeffect_storage[Builtin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `bt = Env MsgGas`
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac next_gas_reading_state >> gvs[] >>
      Cases_on `tr` >> simp[get_storage_def])
  >> Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (Cases_on `bt = Len` >> rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac result_array_length_state >>
      imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >> gvs[] >>
      gvs[supported_exprs_exists_every, listTheory.NOT_EXISTS,
          listTheory.EVERY_MEM] >>
      Cases_on `es` >> gvs[builtin_args_length_ok_def] >> metis_tac[])
  >> simp[Once evaluate_def, type_check_def, assert_def, bind_def,
          ignore_bind_def, raise_def]
QED


Resume eval_mutual_noeffect_storage[TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `type_builtin_args_length_ok tb (LENGTH es)` >>
  rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >>
  first_x_assum drule >> simp[type_check_def, assert_def, return_def]
QED

Resume eval_mutual_noeffect_storage[ExprsNil]:
  simp[Once evaluate_def, return_def]
QED

Resume eval_mutual_noeffect_storage[ExprsCons]:
  rpt strip_tac >>
  qpat_x_assum `eval_exprs cx (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED

Resume eval_mutual_noeffect_storage[BaseName]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
QED

Resume eval_mutual_noeffect_storage[BaseTopLevel]:
  rpt strip_tac >> gvs[Once evaluate_def] >>
  drule lookup_global_state >> simp[]
QED

Resume eval_mutual_noeffect_storage[BaseAttribute]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place cx (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac extend_place_state >> gvs[] >> metis_tac[]
QED

Resume eval_mutual_noeffect_storage[BaseSubscript]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place cx (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
  gvs[] >> metis_tac[]
QED

Resume eval_mutual_noeffect_storage[Target]:
  rpt strip_tac >>
  qpat_x_assum `eval_target_place cx _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac get_place_state >> gvs[] >> metis_tac[]
QED

Resume eval_mutual_noeffect_storage[ResultsNil]:
  simp[Once evaluate_def, return_def]
QED

Resume eval_mutual_noeffect_storage[ResultsCons]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr_results cx (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> metis_tac[]
QED

Finalise eval_mutual_noeffect_storage

Theorem eval_expr_noeffect_storage:
  !cx e s res s' tr.
    ~expr_has_effect e /\ eval_expr cx e s = (res,s') ==>
    get_storage cx s' tr = get_storage cx s tr
Proof
  metis_tac[eval_mutual_noeffect_storage]
QED

Theorem eval_expr_read_noeffect_storage:
  !cx e s res s' tr.
    ~expr_has_effect e /\
    (do raw <- eval_expr cx e; read_result cx raw od) s = (res,s') ==>
    get_storage cx s' tr = get_storage cx s tr
Proof
  rpt gen_tac >> simp[bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  drule_all eval_expr_noeffect_storage >> simp[]
QED

Theorem eval_base_place_noeffect_storage:
  !cx bt s res s' tr.
    ~supported_target_exists expr_effect_root bt /\
    eval_base_place cx bt s = (res,s') ==>
    get_storage cx s' tr = get_storage cx s tr
Proof
  metis_tac[eval_mutual_noeffect_storage]
QED
