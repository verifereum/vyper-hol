Theory exprSimNoPop
Ancestors
  exprSimHyps vyperEvalExprPreservesScopesDom vyperInterpreter vyperCreate vyperCreateFrame
  supportedExprTraverse vyperLookup vyperMisc vyperContext vyperState vyperScopePreservation vyperStatePreservation vyperPlaceFrames vyperCallFrame vyperCallOutcomeFrame vyperPlaceResultTyping

Theorem eval_mutual_nopop_scopes[local]:
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:value list). T) /\
  (!cx e. ~expr_has_pop e ==> !st res st'.
    eval_expr cx e st = (res,st') ==> st'.scopes = st.scopes) /\
  (!cx es. ~supported_exprs_exists expr_pop_root es ==> !st res st'.
    eval_exprs cx es st = (res,st') ==> st'.scopes = st.scopes) /\
  (!cx bt. ~target_has_pop bt ==> !st res st'.
    eval_base_place cx bt st = (res,st') ==> st'.scopes = st.scopes) /\
  (!cx bt. ~target_has_pop bt ==> !st res st'.
    eval_target_place cx bt st = (res,st') ==> st'.scopes = st.scopes) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T) /\
  (!cx es. ~supported_exprs_exists expr_pop_root es ==> !st res st'.
    eval_expr_results cx es st = (res,st') ==> st'.scopes = st.scopes)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[expr_has_pop_def, target_has_pop_def, supported_expr_exists_def,
       expr_pop_root_def] >~
  [`eval_expr _ (Name _ _) _ = _`] >-
    (rpt strip_tac >>
     gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
         type_check_def, assert_def, lift_option_type_def, return_def,
         raise_def, AllCaseEqs()]) >~
  [`eval_expr _ (TopLevelName _ _) _ = _`] >-
    (rpt strip_tac >> gvs[Once evaluate_def] >>
     drule lookup_global_scopes >> simp[]) >~
  [`eval_expr _ (FlagMember _ _ _) _ = _`] >-
    (rpt strip_tac >> gvs[Once evaluate_def] >>
     drule lookup_flag_mem_scopes >> simp[]) >~
  [`eval_expr _ (Literal _ _) _ = _`] >-
    (simp[Once evaluate_def, return_def]) >~
  [`eval_expr _ (IfExp _ _ _ _) _ = _`] >-
    (rpt strip_tac >>
     gvs[Once evaluate_def, bind_def, ignore_bind_def,
         switch_BoolV_def, AllCaseEqs(), return_def, raise_def] >>
     imp_res_tac read_result_state >>
     imp_res_tac conditional_result_state >> gvs[] >>
     gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]) >~
  [`eval_expr _ (StructLit _ _ _) _ = _`] >-
    (simp[supported_fields_exists_every, supported_exprs_exists_every,
          listTheory.EXISTS_MAP] >> rpt strip_tac >>
     gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
     metis_tac[]) >~
  [`eval_expr _ (Subscript _ _ _) _ = _`] >-
    (rpt strip_tac >>
     gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
     imp_res_tac read_result_state >> imp_res_tac select_result_state >>
     gvs[] >> metis_tac[]) >~
  [`eval_expr _ (Attribute _ _ _) _ = _`] >-
    (rpt strip_tac >>
     gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
     imp_res_tac select_result_state >> gvs[] >> metis_tac[]) >~
  [`eval_expr _ (Builtin _ _ _) _ = _`] >- suspend "Builtin" >~
  [`eval_expr _ (TypeBuiltin _ _ _ _) _ = _`] >- suspend "TypeBuiltin" >~
  [`eval_expr _ (Call _ (Send _) _ _) _ = _`] >- suspend "Send" >~
  [`eval_expr _ (Call _ (ExtCall _ _ _ _) _ _) _ = _`] >- suspend "ExtCall" >~
  [`eval_expr _ (Call _ (IntCall _) _ _) _ = _`] >- suspend "IntCall" >~
  [`eval_expr _ (Call _ (RawCallTarget _) _ _) _ = _`] >- suspend "RawCall" >~
  [`eval_expr _ (Call _ (RawCallCalldataTarget _) _ _) _ = _`] >- suspend "RawCalldata" >~
  [`eval_expr _ (Call _ RawLog _ _) _ = _`] >- suspend "RawLog" >~
  [`eval_expr _ (Call _ RawRevert _ _) _ = _`] >- suspend "RawRevert" >~
  [`eval_expr _ (Call _ SelfDestructTarget _ _) _ = _`] >- suspend "SelfDestruct" >~
  [`eval_expr _ (Call _ (CreateTarget _ _ _) _ _) _ = _`] >- suspend "Create" >>
  all_tac >~
  [`eval_exprs _ [] _ = _`] >- suspend "Empty" >~
  [`eval_exprs _ (_::_) _ = _`] >- suspend "Cons" >~
  [`eval_base_place _ (NameTarget _) _ = _`] >- suspend "NamePlace" >~
  [`eval_base_place _ (TopLevelNameTarget _) _ = _`] >- suspend "GlobalPlace" >~
  [`eval_base_place _ (AttributeTarget _ _) _ = _`] >- suspend "AttributePlace" >~
  [`eval_base_place _ (SubscriptTarget _ _) _ = _`] >- suspend "SubscriptPlace" >~
  [`eval_target_place _ _ _ = _`] >- suspend "Target" >~
  [`eval_expr_results _ [] _ = _`] >- suspend "ResultsEmpty" >>
  suspend "ResultsCons"
QED

Resume eval_mutual_nopop_scopes[Builtin]:
    (rpt gen_tac >> strip_tac >>
     Cases_on `builtin_args_length_ok bt (LENGTH es)`
     >- (Cases_on `bt = Len` >> rpt gen_tac >> strip_tac >>
         Cases_on `bt = Env MsgGas` >>
         gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
             assert_def, return_def, raise_def, AllCaseEqs()] >>
         rpt strip_tac >>
         imp_res_tac result_array_length_state >>
         imp_res_tac next_gas_reading_state >>
         imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >> gvs[] >>
         gvs[type_check_def, assert_def, return_def,
             supported_exprs_exists_every, listTheory.EXISTS_MEM,
             builtin_args_length_ok_def] >>
         Cases_on `es` >> gvs[] >> metis_tac[]) >>
     simp[Once evaluate_def, type_check_def, assert_def, bind_def,
          ignore_bind_def, raise_def])
QED

Resume eval_mutual_nopop_scopes[TypeBuiltin]:
    (rpt gen_tac >> strip_tac >>
     Cases_on `type_builtin_args_length_ok tb (LENGTH es)` >>
     rpt gen_tac >> strip_tac >>
     gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
         ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
     rpt strip_tac >> imp_res_tac lift_sum_state >> gvs[] >>
     metis_tac[])
QED

Resume eval_mutual_nopop_scopes[Send]:
    (rpt gen_tac >> strip_tac >>
     Cases_on `LENGTH es = if has_gas then 3 else 2` >>
     simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def] >>
     rpt strip_tac >> gvs[AllCaseEqs(), type_check_def, assert_def, return_def] >>
     imp_res_tac eval_send_preserves_non_accounts >> gvs[] >>
     metis_tac[])
QED

Resume eval_mutual_nopop_scopes[ExtCall]:
    (rpt strip_tac >>
     qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
     strip_tac >> imp_res_tac eval_ext_call_preserves_non_accounts >>
     imp_res_tac read_results_state >> gvs[] >>
     gvs[supported_exprs_exists_every] >>
     `!n. EVERY ($~ o supported_expr_exists expr_pop_root) (TAKE n es)` by
       simp[rich_listTheory.EVERY_TAKE] >>
     `!n. EVERY ($~ o supported_expr_exists expr_pop_root) (DROP n es)` by
       simp[rich_listTheory.EVERY_DROP] >>
     `!n m. EVERY ($~ o supported_expr_exists expr_pop_root) (TAKE n (DROP m es))` by
       simp[rich_listTheory.EVERY_TAKE] >>
     gvs[] >>
     rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac) >>
     rpt (qpat_x_assum `!a b c. _` drule_all >> strip_tac) >>
     metis_tac[])
QED

Resume eval_mutual_nopop_scopes[IntCall]:
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!s t s1 ts t1 s2 tup t2 s3 t3 s4 vs t4 s5 prev t5 s6 t6. _` kall_tac >>
     qpat_x_assum `!s t s1 ts t1 s2 tup t2 s3 t3. _`
       (mp_tac o SRULE [type_check_def, assert_def, lift_option_type_def,
                        option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
     disch_then assume_tac >>
     rpt strip_tac >>
     qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
     rewrite_tac[Once evaluate_def, ignore_bind_def] >>
     simp[bind_def, AllCaseEqs(), return_def, LET_THM] >>
     rpt strip_tac >>
     imp_res_tac type_check_scopes >>
     imp_res_tac lift_option_type_scopes >>
     imp_res_tac finally_set_scopes >>
     imp_res_tac read_results_state >>
     imp_res_tac (SRULE[ignore_bind_def] finally_conditional_lock_scopes) >>
     gvs[] >>
     rpt (qpat_x_assum `type_check _ _ _ = _`
       (strip_assume_tac o SRULE[type_check_def, assert_def,
                                return_def, raise_def, AllCaseEqs()])) >>
     rpt (qpat_x_assum `lift_option_type _ _ _ = _`
       (strip_assume_tac o SRULE[lift_option_type_def, option_CASE_rator,
                                return_def, raise_def, AllCaseEqs()])) >>
     rpt (qpat_x_assum `get_scopes _ = _`
       (strip_assume_tac o SRULE[get_scopes_def, return_def])) >>
     gvs[] >>
     qpat_x_assum `!st res st'. eval_expr_results _ _ _ = _ ==> _` drule >>
     disch_tac >>
     rpt (qpat_x_assum `finally _ _ _ = _` kall_tac) >>
     gvs[push_function_def, return_def, AllCaseEqs()] >>
     gvs[COND_RATOR, option_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
     drule acquire_nonreentrant_lock_scopes >> simp[])
QED

Resume eval_mutual_nopop_scopes[RawCall]:
    (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
          return_def, raise_def, type_check_def, assert_def,
          lift_option_type_def, option_CASE_rator] >>
     rpt strip_tac >> gvs[] >>
     imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[])
QED

Resume eval_mutual_nopop_scopes[RawCalldata]:
    (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
          return_def, raise_def, type_check_def, assert_def,
          lift_option_type_def, option_CASE_rator] >>
     rpt strip_tac >> gvs[] >>
     imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[])
QED

Resume eval_mutual_nopop_scopes[RawLog]:
    (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
          return_def, raise_def, check_def, type_check_def, assert_def,
          lift_option_def, lift_option_type_def, push_log_def, option_CASE_rator] >>
     strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >> metis_tac[])
QED

Resume eval_mutual_nopop_scopes[RawRevert]:
    (rpt strip_tac >>
     gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
         return_def, raise_def, check_def, type_check_def, assert_def] >>
     metis_tac[])
QED

Resume eval_mutual_nopop_scopes[SelfDestruct]:
    (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
          return_def, raise_def, check_def, type_check_def, assert_def,
          lift_option_def, lift_option_type_def, get_accounts_def, option_CASE_rator] >>
     strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
     imp_res_tac transfer_value_scopes >> gvs[] >> metis_tac[])
QED

Resume eval_mutual_nopop_scopes[Create]:
    (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
     gvs[supported_exprs_exists_every] >>
     `!n. EVERY ($~ o supported_expr_exists expr_pop_root) (TAKE n es)` by
       simp[rich_listTheory.EVERY_TAKE] >>
     `!n. EVERY ($~ o supported_expr_exists expr_pop_root) (DROP n es)` by
       simp[rich_listTheory.EVERY_DROP] >>
     `!n m. EVERY ($~ o supported_expr_exists expr_pop_root) (TAKE n (DROP m es))` by
       simp[rich_listTheory.EVERY_TAKE] >>
     `!n m. EVERY ($~ o supported_expr_exists expr_pop_root) (DROP n (DROP m es))` by
       simp[rich_listTheory.EVERY_DROP] >>
     Cases_on `kind` >> gvs[] >>
     gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
     rpt strip_tac >>
     imp_res_tac check_create_blueprint_result_state >> gvs[] >>
     imp_res_tac read_results_state >> gvs[] >>
     imp_res_tac eval_create_preserves_scopes_immutables >> gvs[] >>
     rpt (qpat_x_assum `!s prefix t s1 code_size t1. _` drule_all >> strip_tac) >>
     rpt (qpat_x_assum `!s prefix t s1 results t1 s2 args t2. _` drule_all >> strip_tac) >>
     rpt (qpat_x_assum `!s prefix t. _` drule_all >> strip_tac) >>
     metis_tac[])
QED

Resume eval_mutual_nopop_scopes[Empty]:
  simp[Once evaluate_def, return_def]
QED

Resume eval_mutual_nopop_scopes[Cons]:
    (rpt strip_tac >>
     qpat_x_assum `eval_exprs _ (_::_) _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
     strip_tac >> imp_res_tac read_result_state >> gvs[] >> metis_tac[])
QED

Resume eval_mutual_nopop_scopes[NamePlace]:
    (rpt strip_tac >>
     gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
         type_check_def, assert_def, return_def, raise_def,
         lift_option_type_def, AllCaseEqs()])
QED

Resume eval_mutual_nopop_scopes[GlobalPlace]:
    (rpt strip_tac >> gvs[Once evaluate_def] >>
     drule lookup_global_scopes >> simp[])
QED

Resume eval_mutual_nopop_scopes[AttributePlace]:
    (rpt strip_tac >>
     qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac extend_place_state >> gvs[] >> metis_tac[])
QED

Resume eval_mutual_nopop_scopes[SubscriptPlace]:
    (rpt strip_tac >>
     qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
     gvs[] >> metis_tac[])
QED

Resume eval_mutual_nopop_scopes[Target]:
  rpt strip_tac >> qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac get_place_state >> gvs[] >> metis_tac[]
QED

Resume eval_mutual_nopop_scopes[ResultsEmpty]:
  simp[Once evaluate_def, return_def]
QED

Resume eval_mutual_nopop_scopes[ResultsCons]:
  rpt strip_tac >> qpat_x_assum `eval_expr_results _ (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Finalise eval_mutual_nopop_scopes

Theorem eval_expr_nopop_scopes:
  !cx e st res st'. ~expr_has_pop e /\
    eval_expr cx e st = (res,st') ==> st'.scopes = st.scopes
Proof
  metis_tac[cj 5 eval_mutual_nopop_scopes]
QED

Theorem eval_exprs_nopop_scopes:
  !cx es st res st'. ~supported_exprs_exists expr_pop_root es /\
    eval_exprs cx es st = (res,st') ==> st'.scopes = st.scopes
Proof
  metis_tac[cj 6 eval_mutual_nopop_scopes]
QED

Theorem eval_base_place_nopop_scopes:
  !cx target st res st'. ~target_has_pop target /\
    eval_base_place cx target st = (res,st') ==> st'.scopes = st.scopes
Proof
  metis_tac[cj 7 eval_mutual_nopop_scopes]
QED

Theorem eval_target_place_nopop_scopes:
  !cx target st res st'. ~target_has_pop target /\
    eval_target_place cx target st = (res,st') ==> st'.scopes = st.scopes
Proof
  metis_tac[cj 8 eval_mutual_nopop_scopes]
QED

Theorem eval_expr_results_nopop_scopes:
  !cx es st res st'. ~supported_exprs_exists expr_pop_root es /\
    eval_expr_results cx es st = (res,st') ==> st'.scopes = st.scopes
Proof
  metis_tac[cj 11 eval_mutual_nopop_scopes]
QED
