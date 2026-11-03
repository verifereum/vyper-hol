Theory exprNoPopScopes
Ancestors
  exprSimHyps vyperPlaceResultTyping vyperEvalExprPreservesScopesDom
  vyperInterpreter supportedExprTraverse vyperState vyperContext
  vyperStatePreservation vyperScopePreservation vyperPlaceFrames
  vyperCallFrame vyperCreateFrame

Theorem eval_mutual_nopop_scopes[local]:
  (!cx:evaluation_context. !s:stmt. T) /\
  (!cx:evaluation_context. !ss:stmt list. T) /\
  (!cx:evaluation_context. !it:iterator. T) /\
  (!cx:evaluation_context. !tv:type_value. !id:string. !body:stmt list. !vs:value list. T) /\
  (!cx e st res st'. ~expr_has_pop e /\ eval_expr cx e st = (res,st') ==>
    st'.scopes = st.scopes) /\
  (!cx es st res st'. ~supported_exprs_exists expr_pop_root es /\
    eval_exprs cx es st = (res,st') ==> st'.scopes = st.scopes) /\
  (!cx bt st res st'. ~target_has_pop bt /\ eval_base_place cx bt st = (res,st') ==>
    st'.scopes = st.scopes) /\
  (!cx bt st res st'. ~target_has_pop bt /\ eval_target_place cx bt st = (res,st') ==>
    st'.scopes = st.scopes) /\
  (!cx:evaluation_context. !g:assignment_target. !v:value. T) /\
  (!cx:evaluation_context. !gs:assignment_target list. !vs:value list. T) /\
  (!cx es st res st'. ~supported_exprs_exists expr_pop_root es /\
    eval_expr_results cx es st = (res,st') ==> st'.scopes = st.scopes)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[expr_has_pop_def, target_has_pop_def,
       supported_expr_exists_def, expr_pop_root_def]
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
  >- suspend "Send"
  >- suspend "ExtCall"
  >- suspend "IntCall"
  >- suspend "RawCall"
  >- suspend "RawCall"
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, check_def, type_check_def, assert_def, lift_option_def,
           lift_option_type_def, push_log_def, vyperMiscTheory.option_CASE_rator] >>
      strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, check_def, type_check_def, assert_def] >> metis_tac[])
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, check_def, type_check_def, assert_def, lift_option_def,
           lift_option_type_def, get_accounts_def, vyperMiscTheory.option_CASE_rator] >>
      strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac transfer_value_scopes >> gvs[] >> metis_tac[])
  >- suspend "CreateTarget"
  >- simp[Once evaluate_def, return_def]
  >- (rpt strip_tac >>
      qpat_x_assum `eval_exprs cx (_::_) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      strip_tac >> imp_res_tac read_result_state >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()])
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      drule lookup_global_scopes >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `eval_base_place cx (AttributeTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac extend_place_state >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      qpat_x_assum `eval_base_place cx (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
      gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      qpat_x_assum `eval_target_place cx _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac get_place_state >> gvs[] >> metis_tac[])
  >- simp[Once evaluate_def, return_def]
  >> rpt strip_tac >>
  qpat_x_assum `eval_expr_results cx (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> metis_tac[]
QED

Resume eval_mutual_nopop_scopes[CreateTarget]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `!m n. ~supported_exprs_exists expr_pop_root (TAKE n (DROP m es)) /\
          ~supported_exprs_exists expr_pop_root (DROP n (DROP m es))` by
    (gvs[supported_exprs_exists_every, listTheory.NOT_EXISTS] >>
     metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]) >>
  `!n. ~supported_exprs_exists expr_pop_root (TAKE n es)` by
    (gvs[supported_exprs_exists_every, listTheory.NOT_EXISTS] >>
     metis_tac[rich_listTheory.EVERY_TAKE]) >>
  `!n. ~supported_exprs_exists expr_pop_root (DROP n es)` by
    (gvs[supported_exprs_exists_every, listTheory.NOT_EXISTS] >>
     metis_tac[rich_listTheory.EVERY_DROP]) >>
  Cases_on `kind` >> gvs[] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac check_create_blueprint_result_state >> gvs[] >>
  imp_res_tac read_results_state >> gvs[] >>
  res_tac >>
  imp_res_tac eval_create_preserves_scopes_immutables >> gvs[] >>
  metis_tac[]
QED

Resume eval_mutual_nopop_scopes[ExtCall]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr cx (Call _ (ExtCall _ _ _ _) _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> imp_res_tac eval_ext_call_preserves_non_accounts >>
  imp_res_tac read_results_state >> gvs[] >>
  gvs[supported_exprs_exists_every, listTheory.NOT_EXISTS] >>
  rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!a b c. _` drule_all >> strip_tac) >>
  metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]
QED

Resume eval_mutual_nopop_scopes[Builtin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (Cases_on `bt = Len` >> rpt gen_tac >> strip_tac >>
      Cases_on `bt = Env MsgGas` >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac result_array_length_state >>
      imp_res_tac next_gas_reading_state >>
      imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >> gvs[] >>
      gvs[supported_exprs_exists_every, listTheory.NOT_EXISTS,
          listTheory.EVERY_MEM] >>
      Cases_on `es` >> gvs[builtin_args_length_ok_def] >> metis_tac[])
  >> simp[Once evaluate_def, type_check_def, assert_def, bind_def,
          ignore_bind_def, raise_def]
QED

Resume eval_mutual_nopop_scopes[IntCall]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s t s1 ts t1 s2 tup t2 s3 t3 s4 vs t4 s5 prev t5 s6 t6. _` kall_tac >>
  rule_assum_tac (SRULE [type_check_def, assert_def, lift_option_type_def,
    vyperMiscTheory.option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def,
       type_check_def, assert_def, lift_option_type_def,
       vyperMiscTheory.option_CASE_rator, return_def, raise_def,
       AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac finally_set_scopes >>
  imp_res_tac read_results_state >>
  imp_res_tac lift_option_type_scopes >>
  imp_res_tac (SRULE[ignore_bind_def] finally_conditional_lock_scopes) >>
  gvs[get_scopes_def, return_def] >>
  first_assum drule >> strip_tac >> gvs[] >>
  gvs[push_function_def, return_def, AllCaseEqs()] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  gvs[raise_def, return_def] >>
  Cases_on `FST (SND tup)` >> gvs[return_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >> gvs[]
QED

Resume eval_mutual_nopop_scopes[Name]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, lift_option_type_def,
      return_def, raise_def, AllCaseEqs()]
QED

Resume eval_mutual_nopop_scopes[TopLevel]:
  rpt strip_tac >> gvs[Once evaluate_def] >>
  drule lookup_global_scopes >> simp[]
QED

Resume eval_mutual_nopop_scopes[Flag]:
  rpt strip_tac >> gvs[Once evaluate_def] >>
  drule lookup_flag_mem_scopes >> simp[]
QED

Resume eval_mutual_nopop_scopes[IfExp]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def,
      switch_BoolV_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >>
  imp_res_tac conditional_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED

Resume eval_mutual_nopop_scopes[Literal]:
  simp[Once evaluate_def, return_def]
QED

Resume eval_mutual_nopop_scopes[StructLit]:
  rpt strip_tac >>
  gvs[supported_fields_exists_every, supported_exprs_exists_every,
      listTheory.EXISTS_MAP, Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  metis_tac[]
QED

Resume eval_mutual_nopop_scopes[Subscript]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED

Resume eval_mutual_nopop_scopes[Attribute]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED

Resume eval_mutual_nopop_scopes[TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `type_builtin_args_length_ok tb (LENGTH es)` >>
  rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >>
  first_x_assum drule >> simp[type_check_def, assert_def, return_def]
QED

Resume eval_mutual_nopop_scopes[Send]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `LENGTH es = if has_gas then 3 else 2` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  first_x_assum (qspecl_then [`st`, `st`] mp_tac) >>
  simp[type_check_def, assert_def, return_def] >> strip_tac >>
  rpt CASE_TAC >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule eval_send_preserves_non_accounts >> strip_tac >> gvs[]
QED

Resume eval_mutual_nopop_scopes[RawCall]:
  markerLib.RESUME_TAC >>
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, type_check_def, assert_def, lift_option_type_def,
       vyperMiscTheory.option_CASE_rator] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[]
QED

Finalise eval_mutual_nopop_scopes

Theorem eval_expr_nopop_scopes:
  ~expr_has_pop e /\ eval_expr cx e st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  metis_tac[eval_mutual_nopop_scopes]
QED

Theorem eval_exprs_nopop_scopes:
  ~supported_exprs_exists expr_pop_root es /\
  eval_exprs cx es st = (res,st') ==> st'.scopes = st.scopes
Proof
  metis_tac[eval_mutual_nopop_scopes]
QED

Theorem eval_base_place_nopop_scopes:
  ~target_has_pop bt /\ eval_base_place cx bt st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  metis_tac[eval_mutual_nopop_scopes]
QED

Theorem eval_target_place_nopop_scopes:
  ~target_has_pop bt /\ eval_target_place cx bt st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  metis_tac[eval_mutual_nopop_scopes]
QED

Theorem eval_expr_results_nopop_scopes:
  ~supported_exprs_exists expr_pop_root es /\
  eval_expr_results cx es st = (res,st') ==> st'.scopes = st.scopes
Proof
  metis_tac[eval_mutual_nopop_scopes]
QED
