(*
 * The cases of target_subscript_case (targetSubscriptCase), by the
 * target's root and its indices.
 *
 * TOP-LEVEL:
 *   target_subscript_main_case — a local root whose indices pop nothing,
 *                          or a storage root whose indices are all pure
 *   target_subscript_storage_effectful_case — RESIDUAL: a storage root
 *                          with an index that calls or pops
 *   target_subscript_local_pop_case — RESIDUAL: a local root with an index
 *                          that pops
 *)

Theory targetSubscriptSplit
Ancestors
  targetPlaceLive
  targetPlaceSimCasesBase
  exprSimFieldLayout
  exprSimSource
  targetPlaceSimDefs
  stmtSimProps gasSummary gasSummaryCompose gasContext gasExemptCert
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pair vyperMisc
  fragExec  exprSimHyps exprSimBuffer exprSimAttributeFields
  freshWrites stmtLoweringMono targetPlaceSim supportedExprTraverse
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  valueEncoding vyperAST vyperInterpreter vyperState vyperValue
  vyperTypeSystem vyperTypeCallGraph vyperTypeEnv vyperTypeInvariants
  vyperTypeExprSoundness vyperPlaceFrames vyperEvalMisc vyperPureExpr
  vyperScopePreservation vyperStatePreservation vyperCreateFrame
  vyperPlaceResultTyping
  venomState venomInst
Libs
  pairLib

Theorem target_subscript_base_exempt_cert:
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (eval_base_place cx bt) (return ()))
    (es, s0) marks (err, ee) (leaf, sf) ==>
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (eval_base_place cx (SubscriptTarget bt e)) (return ()))
    (es, s0) marks (err, ee) (leaf, sf)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[ignore_bind_def]
QED

Theorem target_subscript_index_exempt_cert:
  gas_marked_exec memory (ctx, func) (eval_base_place cx bt)
    (es, s0) left (INL pv) mid (OK t) /\
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (mid with gas_obs := [], t) right (err, ee) (leaf, sf) ==>
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (eval_base_place cx (SubscriptTarget bt e)) (return ()))
    (es, s0) (left ++ right) (err, ee) (leaf, sf)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_result >>
  goal_assum (drule_at Any) >> simp[] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  pure_once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[ignore_bind_def, bind_assoc]
QED

(* Full-target admissibility projects to the base: every base exception
   propagates unchanged, and every base success is in target_res_ok. *)
Theorem target_subscript_base_admissible:
  gas_admissible (eval_base_place cx (SubscriptTarget bt e))
    target_res_ok es ==>
  gas_admissible (eval_base_place cx bt) target_res_ok es
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[target_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  once_rewrite_tac[evaluate_def] >> simp[bind_def] >>
  disch_then (qspecl_then [`INR y`, `ee`] mp_tac) >> simp[]
QED

Theorem target_subscript_index_admissible:
  gas_admissible (eval_base_place cx (SubscriptTarget bt e))
    target_res_ok es /\
  gas_marked_exec memory (ctx, func) (eval_base_place cx bt)
    (es, s0) marks (INL pv) mid (OK t) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx))
    expr_res_ok (mid with gas_obs := [])
Proof
  simp[gas_admissible_def, gas_marked_exec_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  qpat_x_assum `!gs res ee. _ ==> _`
    (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
  once_rewrite_tac[evaluate_def] >>
  rewrite_tac[GSYM bind_assoc] >> simp[] >>
  disch_then (qspecl_then [`INR y`, `ee`] mp_tac) >>
  gvs[bind_def, target_res_ok_def, expr_res_ok_def]
QED

(* Internal-call defaults use the existing finally_set_scopes boundary
   from vyperScopePreservation; body cleanup additionally unlocks. *)
Theorem target_subscript_unlock_scopes:
  unlock_if_nr cx nr is_view es = (res, ee) ==> ee.scopes = es.scopes
Proof
  Cases_on `nr /\ ~is_view` >>
  simp[unlock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[return_def] >>
  metis_tac[release_nonreentrant_lock_scopes]
QED

Theorem target_subscript_call_cleanup_scopes:
  finally source (ignore_bind (pop_function prev) (unlock_if_nr cx nr is_view))
    es = (res, ee) ==> ee.scopes = prev
Proof
  strip_tac >> drule finally_pop_function_then_scopes >>
  impl_tac >- metis_tac[target_subscript_unlock_scopes] >> simp[]
QED

Theorem target_subscript_nopop_scopes_mutual[local]:
  (!cx:evaluation_context. !s:stmt. T) /\
  (!cx:evaluation_context. !ss:stmt list. T) /\
  (!cx:evaluation_context. !it:iterator. T) /\
  (!cx:evaluation_context. !tv:type_value. !id:string. !body:stmt list. !vs:value list. T) /\
  (!cx e st res st'.
    ~supported_expr_exists (\x. ?ty t. x = Pop ty t) e /\
    eval_expr cx e st = (res,st') ==> st'.scopes = st.scopes) /\
  (!cx es st res st'.
    ~supported_exprs_exists (\x. ?ty t. x = Pop ty t) es /\
    eval_exprs cx es st = (res,st') ==> st'.scopes = st.scopes) /\
  (!cx bt st res st'.
    ~supported_target_exists (\x. ?ty t. x = Pop ty t) bt /\
    eval_base_place cx bt st = (res,st') ==> st'.scopes = st.scopes) /\
  (!cx bt st res st'.
    ~supported_target_exists (\x. ?ty t. x = Pop ty t) bt /\
    eval_target_place cx bt st = (res,st') ==> st'.scopes = st.scopes) /\
  (!cx:evaluation_context. !g:assignment_target. !v:value. T) /\
  (!cx:evaluation_context. !gs:assignment_target list. !vs:value list. T) /\
  (!cx es st res st'.
    ~supported_exprs_exists (\x. ?ty t. x = Pop ty t) es /\
    eval_expr_results cx es st = (res,st') ==> st'.scopes = st.scopes)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[supported_expr_exists_def]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, lift_option_type_def,
          return_def, raise_def, AllCaseEqs()])
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac lookup_global_scopes >> gvs[])
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac lookup_flag_mem_scopes >> gvs[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def,
          switch_BoolV_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac read_result_state >>
      imp_res_tac conditional_result_state >> gvs[] >>
      gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[])
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      fs[supported_exprs_exists_every, supported_fields_exists_every, EXISTS_MAP] >>
      metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac read_result_state >> imp_res_tac select_result_state >>
      gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac select_result_state >> gvs[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `builtin_args_length_ok bt (LENGTH es)`
      >- (Cases_on `bt = Len` >> rpt gen_tac >> strip_tac >>
          Cases_on `bt = Env MsgGas` >>
          gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
              assert_def, return_def, raise_def, AllCaseEqs()] >>
          imp_res_tac result_array_length_state >>
          imp_res_tac next_gas_reading_state >>
          imp_res_tac precompile_call_success_state >>
          imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >> gvs[] >>
          Cases_on `es` >>
          gvs[vyperContextTheory.builtin_args_length_ok_def,
              supported_expr_exists_def] >> metis_tac[])
      >> simp[Once evaluate_def, type_check_def, assert_def, bind_def,
              ignore_bind_def, raise_def])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `type_builtin_args_length_ok tb (LENGTH es)` >>
      rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
          ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac lift_sum_state >> gvs[] >>
      first_x_assum drule >> simp[type_check_def, assert_def, return_def] >>
      metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      Cases_on `LENGTH es = if has_gas then 3 else 2` >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def, raise_def] >>
      first_x_assum (qspecl_then [`st`, `st`] mp_tac) >>
      simp[type_check_def, assert_def, return_def] >> strip_tac >>
      rpt CASE_TAC >> rpt strip_tac >> gvs[] >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      drule eval_send_preserves_non_accounts >> strip_tac >> gvs[] >>
      metis_tac[])
  >- (rpt strip_tac >>
      fs[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS] >>
      `EVERY (\e. ~supported_expr_exists (\x. ?ty t. x = Pop ty t) e)
         (TAKE 1 es)` by metis_tac[EVERY_TAKE] >>
      `EVERY (\e. ~supported_expr_exists (\x. ?ty t. x = Pop ty t) e)
         (TAKE (LENGTH (FST (SND sig))) (DROP 1 es))` by
        metis_tac[EVERY_TAKE, EVERY_DROP] >>
      `EVERY (\e. ~supported_expr_exists (\x. ?ty t. x = Pop ty t) e)
         (DROP (LENGTH (FST (SND sig)) + 1) es)` by metis_tac[EVERY_DROP] >>
      qpat_x_assum `eval_expr cx (Call _ (ExtCall _ _ _ _) _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      strip_tac >> imp_res_tac eval_ext_call_preserves_non_accounts >>
      imp_res_tac read_results_state >> gvs[] >>
      rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac) >>
      rpt (qpat_x_assum `!a b c. _` drule_all >> strip_tac) >>
      metis_tac[])
  >- suspend "IntCall"
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, type_check_def, assert_def, lift_option_type_def,
           option_CASE_rator] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, type_check_def, assert_def, lift_option_type_def,
           option_CASE_rator] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, check_def, type_check_def, assert_def, lift_option_def,
           lift_option_type_def, push_log_def, option_CASE_rator] >>
      strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
          raise_def, check_def, type_check_def, assert_def] >> metis_tac[])
  >- (rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
           raise_def, check_def, type_check_def, assert_def, lift_option_def,
           lift_option_type_def, get_accounts_def, option_CASE_rator] >>
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
      imp_res_tac lookup_global_scopes >> gvs[])
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

Resume target_subscript_nopop_scopes_mutual[CreateTarget]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  fs[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS] >>
  drule_then assume_tac EVERY_TAKE >>
  drule_then assume_tac EVERY_DROP >>
  `!n. EVERY ($~ o supported_expr_exists (\x. ?ty t. x = Pop ty t))
      (TAKE n (DROP 2 es))` by metis_tac[EVERY_TAKE, EVERY_DROP] >>
  `!n. EVERY ($~ o supported_expr_exists (\x. ?ty t. x = Pop ty t))
      (DROP n (DROP 2 es))` by metis_tac[EVERY_DROP] >>
  Cases_on `kind` >> gvs[] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac check_create_blueprint_result_state >> gvs[] >>
  imp_res_tac read_results_state >> gvs[] >>
  imp_res_tac eval_create_preserves_scopes_immutables >> gvs[]
  >> rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac)
  >> rpt (qpat_x_assum `!a b c d e f g h i j. _` drule_all >> strip_tac)
  >> rpt (qpat_x_assum `!a b c. _` drule_all >> strip_tac)
  >> gvs[]
QED

Resume target_subscript_nopop_scopes_mutual[IntCall]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s t s1 ts t1 s2 tup t2 s3 t3 s4 vs t4 s5 prev t5 s6 t6. _` kall_tac >>
  rule_assum_tac (SRULE [type_check_def, assert_def, lift_option_type_def,
                        option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  gvs[bind_def, ignore_bind_def, type_check_def,
      assert_def, lift_option_type_def, option_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac finally_set_scopes >>
  imp_res_tac (target_subscript_call_cleanup_scopes |>
    Q.INST [`is_view` |-> `mut = View \/ mut = Pure`] |>
    SRULE [unlock_if_nr_def, ignore_bind_def]) >>
  imp_res_tac read_results_state >>
  gvs[get_scopes_def] >>
  rpt (qpat_x_assum `!a b c. _` drule_all >> strip_tac) >>
  gvs[return_def, push_function_def] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  rpt IF_CASES_TAC >>
  simp[bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> Cases_on `cx.nonreentrant_slot` >>
  gvs[bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  gvs[]
QED

Finalise target_subscript_nopop_scopes_mutual

Theorem target_subscript_nopop_expr_scopes:
  ~supported_expr_exists (\x. ?ty t. x = Pop ty t) e /\
  eval_expr cx e es = (res, ee) ==> ee.scopes = es.scopes
Proof
  metis_tac[cj 5 target_subscript_nopop_scopes_mutual]
QED

Theorem target_subscript_nopop_exprs_scopes:
  ~supported_exprs_exists (\x. ?ty t. x = Pop ty t) xs /\
  eval_exprs cx xs es = (res, ee) ==> ee.scopes = es.scopes
Proof
  metis_tac[cj 6 target_subscript_nopop_scopes_mutual]
QED

Theorem target_subscript_nopop_base_scopes:
  ~supported_target_exists (\x. ?ty t. x = Pop ty t) bt /\
  eval_base_place cx bt es = (res, ee) ==> ee.scopes = es.scopes
Proof
  metis_tac[cj 7 target_subscript_nopop_scopes_mutual]
QED

Theorem target_subscript_nopop_target_scopes:
  ~supported_target_exists (\x. ?ty t. x = Pop ty t) bt /\
  eval_target_place cx bt es = (res, ee) ==> ee.scopes = es.scopes
Proof
  metis_tac[cj 8 target_subscript_nopop_scopes_mutual]
QED

Theorem target_subscript_nopop_results_scopes:
  ~supported_exprs_exists (\x. ?ty t. x = Pop ty t) xs /\
  eval_expr_results cx xs es = (res, ee) ==> ee.scopes = es.scopes
Proof
  metis_tac[cj 11 target_subscript_nopop_scopes_mutual]
QED

(* A live local path remains live after a successful extension. *)
Theorem target_subscript_extend_memory_live:
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  extend_place cx (PlaceR (MemoryPlace id path)) sb es = (INL pv,ee) ==>
  ee = es /\ pv = PlaceR (MemoryPlace id (path ++ [sb])) /\
  ?w. evaluate_subscripts entry.type entry.value (path ++ [sb]) = INL w
Proof
  strip_tac >>
  qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
  simp[extend_place_def, place_type_value_def, read_place_def,
       get_scopes_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, return_def, raise_def, read_memory_path_def,
       extend_memory_place_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `subscripts_type entry.type path` >>
  gvs[return_def, raise_def] >>
  rename1 `subscripts_type entry.type path = SOME ptv` >>
  Cases_on `evaluate_subscripts ptv v [sb]` >>
  gvs[return_def, raise_def] >>
  drule_all evaluate_subscripts_append >>
  disch_then (qspec_then `[sb]` mp_tac) >> simp[]
QED

Theorem target_subscript_local_base_live:
  !bt cx es pv ee id.
    target_root bt = NameTarget id /\
    ~supported_target_exists (\x. ?ty t. x = Pop ty t) bt /\
    eval_base_place cx bt es = (INL pv,ee) ==>
    ?path entry v. pv = PlaceR (MemoryPlace id path) /\
      lookup_scopes id ee.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[target_root_def, Once evaluate_def, bind_def, ignore_bind_def,
          get_scopes_def, type_check_def, assert_def, return_def,
          raise_def, AllCaseEqs(), optionTheory.IS_SOME_EXISTS] >>
      simp[evaluate_subscripts_def])
  >- simp[target_root_def]
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[target_root_def, supported_expr_exists_def, Once evaluate_def,
       bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >> gvs[]
  >- (drule_all target_subscript_nopop_expr_scopes >> strip_tac >>
      drule read_result_state >> strip_tac >> gvs[] >>
      drule_at (Pat `extend_place _ _ _ _ = _`)
        target_subscript_extend_memory_live >>
      simp[] >> strip_tac >> gvs[] >> metis_tac[])
  >> drule_all target_subscript_extend_memory_live >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem target_subscript_local_index_live:
  target_root bt = NameTarget id /\
  ~supported_target_exists (\x. ?ty t. x = Pop ty t) (SubscriptTarget bt e) /\
  eval_base_place cx bt es = (INL pv,mid) /\
  bind (eval_expr cx e) (read_result cx) mid = (res,ee) ==>
  ?path entry v. pv = PlaceR (MemoryPlace id path) /\
    lookup_scopes id ee.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL v
Proof
  simp[supported_expr_exists_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >>
  drule_all target_subscript_local_base_live >> strip_tac >>
  drule_all target_subscript_nopop_expr_scopes >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED

Theorem target_subscript_pure_index_live:
  EVERY pure_expr (target_indices (SubscriptTarget bt e)) /\
  eval_base_place cx bt es = (INL pv,mid) /\
  bind (eval_expr cx e) (read_result cx) mid = (res,ee) ==>
  mid = es /\ ee = es /\ nested_pop_result_live cx ee pv
Proof
  simp[target_indices_def, EVERY_APPEND, bind_def, AllCaseEqs()] >>
  rpt strip_tac >>
  drule_all nested_pop_eval_base_live >> strip_tac >>
  drule_all nested_pop_eval_base_pure_state >> strip_tac >> gvs[] >>
  drule_all eval_expr_preserves_state >> strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> gvs[]
QED

Theorem target_subscript_base_exception:
  gas_marked_exec memory (ctx, func) (eval_base_place cx bt)
    (es, s0) marks (INR exc) fin r ==>
  gas_marked_exec memory (ctx, func)
    (eval_base_place cx (SubscriptTarget bt e))
    (es, s0) marks (INR exc) fin r
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >>
  irule gas_marked_exec_bind_exception >> simp[]
QED

(* An element of an array or a mapping, when no index can shrink an array
   the place is already in: the base's fragment, the index's (lower_value),
   then, by the base's place type, the slot of the key
   (compile_mapping_subscript, with compile_keccak256_key for a bytes or
   string key) or the bounds check and the element's pointer
   (compile_array_subscript).  What it takes:
   - the index runs after the base, so the base's target_post must survive
     its fragment: place_ptr_rel does (place_ptr_rel_vars_frame: the local
     pointers and the base's operand are not fresh at the index's start);
     place_readable does too, as without a pop the index leaves the source
     locals as they were (a call restores the caller's scopes);
   - for a storage root, every index is pure, so the source state is the
     one the target started from, and the base's place is read live
     (targetPlaceLive's nested_pop_eval_base_live), so the header the
     bounds check loads is one stmt_state_rel relates;
   - the bounds check: a source RuntimeError for an index out of range
     (evaluate_subscripts array_index for a local's place,
     resolve_array_element's checks for a storage one) against
     compile_array_subscript's ASSERT, which aborts, and an index in range
     against the length the loader reads (an MLOAD at the base's pointer,
     an SLOAD or TLOAD at its slot);
   - the mapping slot: compile_mapping_subscript's SHA3 over the slot and
     key words in a fresh 64-byte buffer against hashmap_slot slot
     (encode_hashmap_key kt kv).
   Given those, the element's place is at the base's pointer plus the
   element's offset (mem_step_offset) for a local, and at the element's
   slot for storage. *)
Theorem target_subscript_main_case:
  !nocalls ctx func cenv cx bt e.
    target_case nocalls ctx func cenv cx bt /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv, s1)) ==>
     expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e) /\
    (!nsid. target_root bt = TopLevelNameTarget nsid ==>
            EVERY pure_expr (target_indices (SubscriptTarget bt e))) /\
    (!id. target_root bt = NameTarget id ==>
          ~supported_target_exists (\x. ?ty t. x = Pop ty t)
             (SubscriptTarget bt e)) ==>
    target_case nocalls ctx func cenv cx (SubscriptTarget bt e)
Proof
  cheat
QED

(* RESIDUAL (effectful storage indices): an index that calls or pops can
   shrink an array the target already points into (outer[0][shrink()] = v,
   or with the call in an index of the base), so the header the bounds
   check reads can be dead.  Source and Venom read the same raw slot, but
   stmt_state_rel relates only live storage (storage_dead).  Needs raw
   agreement on slots made dead by a write; exprSimPopNestedStorageEffectful's
   pop_nested_storage_effectful_sim has the same exposure.  The root is any
   module name, so this also covers an immutable's member in the
   constructor, which a call in an index can pop (es.immutables is
   module-wide; a call restores only the scopes); target_pre excludes such
   a root (immutable_root), so its pure case needs nothing. *)
Theorem target_subscript_storage_effectful_case:
  !nocalls ctx func cenv cx bt e nsid.
    target_case nocalls ctx func cenv cx bt /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv, s1)) ==>
     expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e) /\
    target_root bt = TopLevelNameTarget nsid /\
    ~EVERY pure_expr (target_indices (SubscriptTarget bt e)) ==>
    target_case nocalls ctx func cenv cx (SubscriptTarget bt e)
Proof
  cheat
QED

(* RESIDUAL (a pop in a local target's index): the pop can pop an ancestor
   of the base (x[0][len(x.pop()) - 1] = v).  The compiled pointer then
   points at memory the pop left in place, and the source reads the base
   through read_memory_path's popped history, but no invariant relates the
   popped history to memory yet.  exprSimPopNested's pop_nested_local_sim
   is of the same family. *)
Theorem target_subscript_local_pop_case:
  !nocalls ctx func cenv cx bt e id.
    target_case nocalls ctx func cenv cx bt /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv, s1)) ==>
     expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e) /\
    target_root bt = NameTarget id /\
    supported_target_exists (\x. ?ty t. x = Pop ty t) (SubscriptTarget bt e) ==>
    target_case nocalls ctx func cenv cx (SubscriptTarget bt e)
Proof
  cheat
QED
