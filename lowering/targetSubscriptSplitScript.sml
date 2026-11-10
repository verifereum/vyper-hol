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
  targetPlaceLive targetSubscriptMemory targetSubscriptDecode targetSubscriptContinuation
  targetPlaceSimCasesBase exprReasonOperand exprSimPopNestedLocalHandoff
  exprSimFieldLayout exprSafeOperandBuiltins exprSafeOperand
  exprSimSource
  targetPlaceSimDefs
  stmtSimProps gasOutcome gasSummary gasSummaryCompose gasContext gasExemptCert
  fragGasMode fragGasPath
  exprSimProps exprBopSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pair vyperMisc
  fragExec  exprSimHyps exprSimBuffer exprSimAttributeFields
  freshWrites stmtLoweringMono targetPlaceSim supportedExprTraverse
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv loweringStateRelDefs
  valueEncoding vyperAST vyperInterpreter vyperCallOutcomeFrame vyperState vyperValue
  vyperTypeSystem vyperTypeCallGraph vyperTypeEnv vyperTypeInvariants
  vyperTypeExprSoundness vyperPlaceFrames vyperEvalMisc vyperPureExpr
  vyperScopePreservation vyperStatePreservation vyperCreateFrame
  vyperEvalExprPreservesScopesDom
  vyperPlaceResultTyping
  venomState venomInst
Libs
  pairLib

Theorem target_post_index_frame:
  target_post ctx func cenv cx es sa sm s0 es1 pv vt rb t /\
  expr_post ctx func cenv cx e es1 sm sn t es2 v ix u /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  place_readable cx es2 pv /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ (!l. FST rb <> Label l) ==>
  target_post ctx func cenv cx es sa sn s0 es2 pv vt rb u
Proof
  simp[target_post_def, expr_post_def] >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `!x. not_fresh_at sm x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  simp[] >> rpt conj_tac
  >- (qexists `w` >> conj_tac
      >- (irule eval_operand_frame >> simp[] >> qexistsl [`sm`, `t`] >> simp[]) >>
      irule target_place_ptr_values_frame >> qexistsl [`t`, `sm`] >> simp[])
  >- (rpt strip_tac >>
      `local_ptrs_rel func cenv es.scopes s0` by
        fs[stmt_state_rel_def, state_rel_def] >>
      `!n b sz'. local_region cenv es1.scopes t n b sz' ==>
                  off + sz <= b \/ b + sz' <= off` by
        (rpt strip_tac >>
         qpat_x_assum `!n b sz'. local_region cenv es.scopes s0 _ _ _ ==> _` irule >>
         qexists `n` >> irule local_region_frame >>
         conj_tac >- (qexists `func` >> simp[]) >>
         qexistsl [`sa`, `es1.scopes`, `t`] >> simp[]) >>
      `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `aid < sm.cs_next_id` by decide_tac >> metis_tac[]) >>
  irule locals_kept_trans >> qexistsl [`es1`, `sa`, `t`] >> simp[]
QED

Theorem target_subscript_index_sim:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  eval_base_place cx bt es = (INL pv,es1) /\
  (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) /\
  ((?s p s1. eval_base_place cx bt s = (INL p,s1)) ==>
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_vv_case nocalls ctx func cenv cx e) ==>
  expr_sim ctx func cenv cx ty e es1 /\
  expr_vv_sim ctx func cenv cx ty e es1
Proof
  strip_tac >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `expr_sim_inv cenv cx env es1` by metis_tac[eval_base_place_sim_inv] >>
  `expr_body_pre cenv cx env e es1` by
    fs[target_pre_def, target_indices_pre_def] >>
  `expr_sim_case nocalls ctx func cenv cx e /\
   expr_vv_case nocalls ctx func cenv cx e` by metis_tac[] >>
  gvs[expr_sim_case_def, expr_vv_case_def, int_calls_expr_def] >>
  metis_tac[]
QED

(* The counted index keeps the original source computation and error post.
   Readability is a source preservation premise, supplied separately by the
   local no-Pop or storage pure-index boundary. *)
Theorem target_index_outcome:
  target_post ctx func cenv cx es sa sm s0 es1 pv vt rb t /\
  expr_sim ctx func cenv cx (expr_type e) e es1 /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es1 /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (!gs v ee. bind (eval_expr cx e) (read_result cx)
       (es1 with gas_obs := gs) = (INL v,ee) ==> place_readable cx ee pv) /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ (!l. FST rb <> Label l) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es1,t)
    (\res ee u. ?v. res = INL v /\
       target_post ctx func cenv cx es sa sn s0 ee pv vt rb u /\
       expr_post ctx func cenv cx e es1 sm sn t ee v ix u /\
       u.vs_current_bb = sn.cs_current_bb /\
       u.vs_inst_idx = LENGTH sn.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_def] >>
  disch_then (qspecl_then [`sm`, `sn`, `ix`, `t`] mp_tac) >>
  impl_tac >- fs[target_post_def] >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (qexists `marks` >> disj1_tac >> gvs[] >>
      qexistsl [`INL v`, `es_end`, `OK t'`] >> simp[] >>
      `place_readable cx (es_end with gas_obs := []) pv` by
        (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
         simp[gas_marked_exec_def] >> strip_tac >>
         first_x_assum (qspec_then `[]` mp_tac) >>
         metis_tac[]) >>
      drule_all target_post_index_frame >> simp[]) 
  >- (qexists `marks` >> disj1_tac >>
      qexistsl [`res`, `es_end`, `r`] >> simp[]) >>
  qexists `marks` >> disj2_tac >> metis_tac[]
QED

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
          Cases_on `bt = Bop In \/ bt = Bop NotIn` >>
          gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
              assert_def, return_def, raise_def, AllCaseEqs()] >>
          imp_res_tac result_array_length_state >>
          imp_res_tac next_gas_reading_state >>
          imp_res_tac precompile_call_success_state >>
          imp_res_tac lift_option_type_state >>
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
  (* the case split on the one hypothesis, not gvs over every assumption
     with AllCaseEqs(), which runs over the step budget *)
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, lift_option_type_def, option_CASE_rator,
       return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
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
        extend_place_memory_live >>
      simp[] >> strip_tac >> gvs[] >> metis_tac[])
  >> drule_all extend_place_memory_live >>
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

Theorem target_subscript_extend_gas_obs:
  !cx pv key es gs.
    extend_place cx pv (ValueSubscript key) (es with gas_obs := gs) =
      (FST (extend_place cx pv (ValueSubscript key) es), es with gas_obs := gs)
Proof
  rpt gen_tac >> Cases_on `pv`
  >~ [`PlaceR p`]
  >- (Cases_on `p`
      >~ [`StoragePlace tr slot tv`]
      >- (Cases_on `tv` >> Cases_on `key` >>
          simp[extend_place_def, extend_storage_place_def, bind_def,
               ignore_bind_def, return_def, raise_def, check_def,
               lift_option_type_def, assert_def, resolve_array_element_def,
               get_storage_backend_def, get_accounts_def,
               get_transient_storage_def]
          >~ [`oEL (Num i) tvs`]
          >- (Cases_on `0 <= i /\ Num i < LENGTH tvs` >>
              Cases_on `oEL (Num i) tvs` >> simp[return_def, raise_def]) >>
          Cases_on `b` >> Cases_on `tr` >>
          simp[get_storage_backend_def, get_accounts_def,
               get_transient_storage_def, bind_def, return_def, assert_def,
               resolve_array_element_def] >>
          rpt IF_CASES_TAC >> simp[return_def, raise_def] >>
          Cases_on `t` >> simp[resolve_array_element_def, return_def]) >>
      simp[extend_place_def, place_type_value_def, read_place_def,
           get_scopes_def, get_immutables_def, get_address_immutables_def,
           bind_def, ignore_bind_def, return_def, raise_def,
           lift_option_type_def, lift_sum_def]
      >~ [`lookup_scopes _ es.scopes`]
      >- (rename1 `lookup_scopes id es.scopes` >>
          Cases_on `lookup_scopes id es.scopes` >>
          simp[return_def, raise_def] >>
          rename1 `subscripts_type entry.type path` >>
          Cases_on `subscripts_type entry.type path` >>
          simp[return_def, raise_def] >>
          Cases_on `read_memory_path entry path` >>
          simp[return_def, raise_def] >>
          rename1 `evaluate_subscripts tv v [ValueSubscript key]` >>
          Cases_on `evaluate_subscripts tv v [ValueSubscript key]` >>
          simp[return_def, raise_def]) >>
      rename1 `ALOOKUP es.immutables cx.txn.target` >>
      Cases_on `ALOOKUP es.immutables cx.txn.target` >>
      simp[return_def, raise_def] >>
      rename1 `FLOOKUP (get_source_immutables src imms) id` >>
      Cases_on `FLOOKUP (get_source_immutables src imms) id` >>
      simp[return_def, raise_def] >>
      rename1 `subscripts_type (FST tva) path` >>
      Cases_on `subscripts_type (FST tva) path` >>
      simp[return_def, raise_def] >>
      Cases_on `evaluate_subscripts (FST tva) (SND tva) path` >>
      simp[return_def, raise_def] >>
      rename1 `evaluate_subscripts tv v [ValueSubscript key]` >>
      Cases_on `evaluate_subscripts tv v [ValueSubscript key]` >>
      simp[return_def, raise_def]) >>
  simp[extend_place_def, raise_def, bind_def, return_def,
       lift_option_type_def] >>
  Cases_on `v` >> simp[bind_def, return_def] >>
  rename1 `evaluate_type (get_tenv cx) ty` >>
  Cases_on `evaluate_type (get_tenv cx) ty` >> simp[return_def, raise_def]
QED

Theorem target_subscript_extend_summary_normal:
  extend_place cx pv (ValueSubscript key) es = (INL pv',es') /\
  gas_marked_path F ctx func s 0 (OK u) /\
  Q (INL pv') (es' with gas_obs := []) u ==>
  gas_summary_at F (ctx,func) [] (extend_place cx pv (ValueSubscript key))
    (es,s) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule extend_place_state >> strip_tac >> gvs[] >>
  simp[gas_summary_at_def] >>
  qexistsl [`INL pv'`, `es`, `OK u`] >>
  simp[gas_marked_exec_def, target_subscript_extend_gas_obs]
QED

Theorem target_subscript_extend_summary_error:
  extend_place cx pv (ValueSubscript key) es = (INR err,es') /\
  gas_marked_path F ctx func s 0 r /\
  exit_result r /\ expr_exit (INR err) r ==>
  gas_summary_at F (ctx,func) [] (extend_place cx pv (ValueSubscript key))
    (es,s) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule extend_place_state >> strip_tac >> gvs[] >>
  simp[gas_summary_at_def] >>
  qexistsl [`INR err`, `es`, `r`] >>
  simp[gas_marked_exec_def, target_subscript_extend_gas_obs] >>
  disj2_tac >> gvs[oneline expr_exit_def, AllCaseEqs()]
QED

(* A successful index is followed by a no-observation place extension.
   The continuation summary retains the exact source extension computation. *)
Theorem target_subscript_index_bind_outcome:
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (mid,t)
    (\res ee u. ?key. res = INL key /\ P key ee u)
    (\res ee r. expr_exit res r) /\
  (!right key ee u.
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (mid,t) right (INL key) ee (OK u) /\
    P key (ee with gas_obs := []) u ==>
    gas_summary_at F (ctx,func) [] (extend_place cx pv (ValueSubscript key))
      (ee with gas_obs := [],u) Q (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\key. extend_place cx pv (ValueSubscript key)))
    (mid,t) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `right` strip_assume_tac)
  >- (gvs[] >> first_x_assum drule_all >>
      rewrite_tac[gas_summary_at_def] >> strip_tac
      >- (qexists `right` >> disj1_tac >>
          qexistsl [`res`, `es_end'`, `r`] >> conj_tac
          >- (pure_once_rewrite_tac[GSYM APPEND_NIL] >>
              irule gas_marked_exec_bind_normal >>
              goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >> fs[])
      >> qexists `right` >> disj1_tac >>
      qexistsl [`res`, `es_end'`, `r`] >> conj_tac
      >- (pure_once_rewrite_tac[GSYM APPEND_NIL] >>
          irule gas_marked_exec_bind_normal >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >> fs[])
  >- (gvs[] >>
      `?exc. res = INR exc` by (Cases_on `res` >> gvs[expr_exit_def]) >>
      gvs[] >> qexists `right` >> disj1_tac >>
      qexistsl [`INR exc`, `es_end`, `r`] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> gvs[oneline expr_exit_def, AllCaseEqs()]) >>
  qexists `right` >> disj2_tac >>
  rewrite_tac[ignore_bind_def] >> pure_once_rewrite_tac[bind_assoc] >>
  irule_at Any gas_exempt_cert_error_value >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Theorem target_subscript_bind_outcome:
  gas_outcome F (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
    (\res ee t. ?pv. res = INL pv /\ P pv ee t)
    (\res ee r. expr_exit res r) /\
  (!left pv mid t.
    gas_marked_exec F (ctx,func) (eval_base_place cx bt)
      (es,s0) left (INL pv) mid (OK t) /\
    P pv (mid with gas_obs := []) t ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (bind (bind (eval_expr cx e) (read_result cx))
        (\key. extend_place cx pv (ValueSubscript key)))
      (mid with gas_obs := [],t)
      (\res ee u. ?pv'. res = INL pv' /\
        target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_base_place cx (SubscriptTarget bt e)) (es,s0)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (gvs[] >>
      first_x_assum drule_all >>
      rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
      disch_then (qx_choose_then `right` strip_assume_tac)
      >- (qexists `left ++ right` >> disj1_tac >>
          once_rewrite_tac[evaluate_def] >> rewrite_tac[GSYM bind_assoc] >>
          qexistsl [`res`, `es_end'`, `r`] >> conj_tac
          >- (irule gas_marked_exec_bind_normal >>
              goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >> fs[])
      >- (qexists `left ++ right` >> disj1_tac >>
          once_rewrite_tac[evaluate_def] >> rewrite_tac[GSYM bind_assoc] >>
          qexistsl [`res`, `es_end'`, `r`] >> conj_tac
          >- (irule gas_marked_exec_bind_normal >>
              goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >> fs[]) >>
      qexists `left ++ right` >> disj2_tac >>
      once_rewrite_tac[evaluate_def] >>
      rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule_at Any gas_exempt_cert_bind_result >>
      simp[GSYM ignore_bind_def, GSYM bind_assoc] >> metis_tac[])
  >- (gvs[] >>
      `?exc. res = INR exc` by (Cases_on `res` >> gvs[expr_exit_def]) >>
      gvs[] >> qexists `left` >> disj1_tac >>
      metis_tac[target_subscript_base_exception]) >>
  qexists `left` >> disj2_tac >>
  metis_tac[target_subscript_base_exempt_cert]
QED

Theorem target_subscript_pre_gas_obs[simp]:
  target_pre cenv cx env bt (es with gas_obs := gs) <=>
  target_pre cenv cx env bt es
Proof
  simp[target_pre_def]
QED

Theorem target_subscript_marked_base_source:
  gas_marked_exec memory (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) ==>
  !tail. eval_base_place cx bt
    (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
      (INL pv, mid with gas_obs := tail)
Proof
  simp[gas_marked_exec_def]
QED

Theorem target_subscript_marked_index_sim:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) /\
  ((?s p s1. eval_base_place cx bt s = (INL p,s1)) ==>
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_vv_case nocalls ctx func cenv cx e) /\
  gas_marked_exec memory (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) ==>
  expr_sim ctx func cenv cx ty e (mid with gas_obs := []) /\
  expr_vv_sim ctx func cenv cx ty e (mid with gas_obs := [])
Proof
  strip_tac >> drule target_subscript_marked_base_source >>
  disch_then (qspec_then `[]` assume_tac) >>
  irule target_subscript_index_sim >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`env`, `nocalls`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem target_subscript_marked_base_inv:
  target_pre cenv cx env bt es /\
  gas_marked_exec memory (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) ==>
  expr_sim_inv cenv cx env (mid with gas_obs := [])
Proof
  strip_tac >> drule target_subscript_marked_base_source >>
  disch_then (qspec_then `[]` assume_tac) >>
  irule eval_base_place_sim_inv >> goal_assum (drule_at Any) >> simp[]
QED

Theorem target_subscript_marked_base_domains:
  gas_marked_exec memory (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) ==>
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >> drule target_subscript_marked_base_source >>
  disch_then (qspec_then `[]` mp_tac) >>
  disch_then (mp_tac o MATCH_MP eval_base_place_preserves_scopes_dom) >> simp[]
QED

Theorem target_subscript_marked_base_nonhalted:
  gas_marked_exec memory (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) ==> ~t.vs_halted
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  drule gas_marked_path_exec >> strip_tac >>
  metis_tac[gas_path_normal]
QED

Theorem target_subscript_readable_gas_obs[simp]:
  place_readable cx (es with gas_obs := gs) pv <=> place_readable cx es pv
Proof
  Cases_on `pv` >> simp[place_readable_def] >>
  Cases_on `p` >> simp[place_readable_def] >>
  simp[read_place_def, get_scopes_def, bind_def, lift_option_type_def,
       lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `lookup_scopes s es.scopes` >> simp[return_def, raise_def] >>
  Cases_on `read_memory_path x l` >> simp[return_def, raise_def]
QED

Theorem target_subscript_marked_index_readable:
  (!nsid. target_root bt = TopLevelNameTarget nsid ==>
    EVERY pure_expr (target_indices (SubscriptTarget bt e))) /\
  (!id. target_root bt = NameTarget id ==>
    ~supported_target_exists (\x. ?ty t. x = Pop ty t) (SubscriptTarget bt e)) /\
  gas_marked_exec memory (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) /\
  place_readable cx (mid with gas_obs := []) pv ==>
  !gs v ee. bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := gs) = (INL v,ee) ==>
    place_readable cx ee pv
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `(?id. target_root bt = NameTarget id) \/
   (?nsid. target_root bt = TopLevelNameTarget nsid)` by
    (qid_spec_tac `bt` >> recInduct base_assignment_target_induct >>
     simp[target_root_def]) >>
  drule target_subscript_marked_base_source >>
  disch_then (qspec_then `gs` assume_tac) >> gvs[]
  >- (drule_all target_subscript_local_index_live >> strip_tac >> gvs[] >>
      irule place_readable_memory_live >> metis_tac[]) >>
  drule_all target_subscript_pure_index_live >> strip_tac >> gvs[] >>
  qpat_x_assum `mid with gas_obs := gs = _` mp_tac >>
  qpat_x_assum `place_readable cx mid pv` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[target_subscript_readable_gas_obs]
QED

Theorem target_subscript_typed_base_not_label:
  expr_sim_inv cenv cx env es /\
  type_place_target env bt = SOME bvt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) ==>
  !l. FST rb <> Label l
Proof
  Cases_on `bt`
  >~ [`NameTarget id`]
  >- (simp[type_place_target_NameTarget, AllCaseEqs()] >> strip_tac >>
      `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
        metis_tac[expr_sim_inv_def] >>
      gvs[compile_get_target_ptr_def, comp_return_def])
  >~ [`TopLevelNameTarget nsid`]
  >- (simp[compile_get_target_ptr_def] >> rpt strip_tac >>
      Cases_on `FLOOKUP cenv.ce_module_vars nsid` >>
      gvs[comp_return_def] >> Cases_on `x` >> gvs[comp_return_def])
  >~ [`AttributeTarget bt fld`]
  >- (simp[Once compile_get_target_ptr_def, comp_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >>
      drule emit_op_safe_operand >> gvs[safe_operand_def, comp_return_def]) >>
  simp[Once compile_get_target_ptr_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  Cases_on `SND (SND result)` >> gvs[comp_bind_def] >>
  TRY (rename1 `SND (SND result) = SOME pt` >> Cases_on `pt` >>
       gvs[comp_bind_def]) >>
  rpt (pairarg_tac >> gvs[comp_return_def]) >>
  imp_res_tac (cj 1 subscript_pop_not_label) >>
  imp_res_tac (cj 2 subscript_pop_not_label) >> gvs[]
QED

Theorem target_subscript_index_source_diagnostic[local]:
  expr_body_pre cenv cx env e s /\
  bind (eval_expr cx e) (read_result cx) s = (INL key,ee) ==>
  expr_sim_inv cenv cx env ee /\ expr_result_typed env e (Value key)
Proof
  strip_tac >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.expr_body_pre_eval) >>
  simp[]
QED

Theorem target_subscript_index_runtime_diagnostic[local]:
  expr_body_pre cenv cx env e s /\
  bind (eval_expr cx e) (read_result cx) s = (INL key,ee) ==>
  ?itv. evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\
    value_has_type itv key
Proof
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >> strip_tac >>
  drule read_result_state >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem target_subscript_memory_array_ready[local]:
  expr_sim_inv cenv cx env es /\
  target_post ctx func cenv cx es0 sa sn s0 es
    (PlaceR (MemoryPlace id path)) bvt rb s /\
  subscript_vtype bvt ity = SOME vt /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL v ==>
  ?av. v = ArrayV av
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\
   ?w. place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w
      (FST (SND rb)) bvt` by (fs[target_post_def] >> metis_tac[]) >>
  Cases_on `bvt`
  >- (`?tv. evaluate_type (get_tenv cx) t = SOME tv` by fs[place_ptr_rel_def] >>
      drule_all place_ptr_rel_memory_current >> strip_tac >>
      Cases_on `t` >> gvs[subscript_vtype_def, AllCaseEqs()] >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  gvs[place_ptr_rel_def]
QED

Theorem target_subscript_storage_ready[local]:
  storage_layout_safe cx /\ contract_storage_well_formed cx es /\
  EVERY pure_expr (target_indices (SubscriptTarget bt e)) /\
  eval_base_place cx bt es = (INL (PlaceR (StoragePlace tr slot tv)),mid) /\
  bind (eval_expr cx e) (read_result cx) mid = (res,ee) ==>
  storage_read_live cx tr (get_storage cx ee tr) slot tv /\
  w2n slot + type_slot_size tv <= dimword(:256) /\
  (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
     w2n (lookup_storage slot (get_storage cx ee tr)) <= cnt)
Proof
  strip_tac >>
  drule_all target_subscript_pure_index_live >> strip_tac >> gvs[] >>
  `EVERY pure_expr (target_indices bt)` by fs[target_indices_def, EVERY_APPEND] >>
  `storage_read_live cx tr (get_storage cx ee tr) slot tv /\
   w2n slot + type_slot_size tv <= dimword(:256)` by
    (irule target_subscript_storage_base_view >>
     conj_tac >- simp[] >>
     qexistsl [`bt`, `ee`, `ee`] >>
     simp[vyperStorageBackendTheory.get_storage_backend_eq]) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  drule_all target_eval_base_header_capacity >> simp[]
QED

Theorem target_subscript_typed_summary[local]:
  subscript_vtype bvt (expr_type e) = SOME vt /\
  well_formed_vtype (get_tenv cx) vt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME itv /\ value_has_type itv key /\
  target_post ctx func cenv cx es0 sa sn s0 es pv bvt rb s /\
  expr_post ctx func cenv cx e ee sm sn t es key ix s /\
  expr_sim_inv cenv cx env es /\
  (!id path. pv = PlaceR (MemoryPlace id path) ==>
    ?entry av. lookup_scopes id es.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
  (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
    storage_read_live cx tr (get_storage cx es tr) slot tv /\
    w2n slot + type_slot_size tv <= dimword(:256) /\
    (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
       w2n (lookup_storage slot (get_storage cx es tr)) <= cnt)) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) ==>
  gas_summary_at F (ctx,func) [] (extend_place cx pv (ValueSubscript key))
    (es,s)
    (\res es' u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es0 sa sb s0 es' pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res es' r. expr_exit res r)
Proof
  strip_tac >>
  Cases_on `extend_place cx pv (ValueSubscript key) es` >>
  rename1 `extend_place cx pv (ValueSubscript key) es = (result,es')` >>
  Cases_on `result`
  >- (drule_all target_subscript_typed_normal >> strip_tac >>
      irule target_subscript_extend_summary_normal >>
      goal_assum (drule_at Any) >> simp[] >>
      fs[target_post_def] >>
      `locals_kept cenv es0 (es' with gas_obs := []) s0 u <=>
       locals_kept cenv es0 es' s0 u` by
        (rpt (pop_assum kall_tac) >> simp[locals_kept_def, popped_kept_def]) >>
      pop_assum (fn th => rewrite_tac[th]) >>
      rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  drule_all target_subscript_typed_error >> strip_tac >>
  irule target_subscript_extend_summary_error >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `expr_exit (INR _) _` mp_tac >>
  Cases_on `r` >> simp[expr_exit_def, exit_result_def, AllCaseEqs()]
QED

Theorem target_subscript_source_readiness[local]:
  target_pre cenv cx env bt es0 /\
  expr_sim_inv cenv cx env es /\ expr_sim_inv cenv cx env fin /\
  (!nsid. target_root bt = TopLevelNameTarget nsid ==>
    EVERY pure_expr (target_indices (SubscriptTarget bt e))) /\
  (!id. target_root bt = NameTarget id ==>
    ~supported_target_exists (\x. ?ty t. x = Pop ty t) (SubscriptTarget bt e)) /\
  eval_base_place cx bt es = (INL pv,mid) /\
  bind (eval_expr cx e) (read_result cx) mid = (res,fin) /\
  target_post ctx func cenv cx es0 sa sn s0 fin pv bvt rb s /\
  subscript_vtype bvt (expr_type e) = SOME vt ==>
  (!id path. pv = PlaceR (MemoryPlace id path) ==>
    ?entry av. lookup_scopes id fin.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
  (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
    storage_read_live cx tr (get_storage cx fin tr) slot tv /\
    w2n slot + type_slot_size tv <= dimword(:256) /\
    (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
       w2n (lookup_storage slot (get_storage cx fin tr)) <= cnt))
Proof
  strip_tac >>
  `(?id. target_root bt = NameTarget id) \/
   (?src id. target_root bt = TopLevelNameTarget (src,id))` by
    (qid_spec_tac `bt` >> recInduct base_assignment_target_induct >>
     simp[target_root_def] >> Cases_on `nsid` >> simp[])
  >- (`~supported_target_exists (\x. ?ty t. x = Pop ty t)
         (SubscriptTarget bt e)` by metis_tac[] >>
      drule_all target_subscript_local_index_live >> strip_tac >> gvs[] >>
      drule_all target_subscript_memory_array_ready >> strip_tac >>
      gvs[]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      drule stmtSimForArrayFrameTheory.eval_base_place_memory_root >>
      simp[place_access_target_root]) >>
  rpt gen_tac >> disch_tac >> gvs[] >>
  `EVERY pure_expr (target_indices (SubscriptTarget bt e))` by metis_tac[] >>
  `storage_layout_safe cx /\ contract_storage_well_formed cx es` by
    fs[expr_sim_inv_def] >>
  drule_all target_subscript_storage_ready >> simp[]
QED

Theorem target_subscript_suffix_var[local]:
  target_subscript_suffix cenv e rb ix sn = (op,sb) ==>
  !x. FST op = Var x ==> not_fresh_at sb x
Proof
  Cases_on `SND (SND rb)` >>
  simp[target_subscript_suffix_def, LET_THM, comp_bind_def, comp_return_def]
  >- (rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
      metis_tac[exprOperandVarTheory.compiler_subscript_ops_var]) >>
  Cases_on `x` >>
  simp[target_subscript_suffix_def, LET_THM, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[exprOperandVarTheory.compiler_subscript_ops_var]
QED

Theorem target_subscript_vtype_well_formed[local]:
  !tenv base_vt idx_ty result_vt.
    well_formed_vtype tenv base_vt /\
    subscript_vtype base_vt idx_ty = SOME result_vt ==>
    well_formed_vtype tenv result_vt
Proof
  Cases_on `base_vt` >>
  simp[subscript_vtype_def, well_formed_vtype_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `t` >>
      gvs[subscript_vtype_def, well_formed_vtype_def,
          well_formed_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `evaluate_type tenv t'` >> gvs[]) >>
  gvs[]
QED

Theorem target_subscript_target_well_formed[local]:
  !bt env cx st vt. env_consistent env cx st /\
    type_place_target env bt = SOME vt ==> well_formed_vtype env.type_defs vt
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> BETA_TAC >> rpt gen_tac
  >- (simp[type_place_target_NameTarget] >> rpt strip_tac >> gvs[] >>
      gvs[env_consistent_def, env_scopes_consistent_def] >>
      first_x_assum drule >> strip_tac >>
      qpat_x_assum `!id ty entry. _ ==> evaluate_type _ _ = _`
        (drule_all_then assume_tac) >>
      fs[env_context_consistent_def, well_formed_vtype_def,
         well_formed_type_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[])
  >- (rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      simp[type_place_target_TopLevelNameTarget] >>
      rpt strip_tac >> gvs[env_consistent_def, env_context_consistent_def] >>
      metis_tac[])
  >- (simp[type_place_target_SubscriptTarget] >> rpt strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      metis_tac[target_subscript_vtype_well_formed]) >>
  simp[type_place_target_AttributeTarget] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  gvs[well_formed_vtype_def, well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  drule_all attribute_type_runtime_step >> strip_tac >> metis_tac[]
QED

Theorem target_subscript_pre_result_well_formed[local]:
  target_pre cenv cx env bt es /\ type_place_target env bt = SOME vt ==>
  well_formed_vtype (get_tenv cx) vt
Proof
  strip_tac >>
  `env_consistent env cx es` by fs[target_pre_def, expr_sim_inv_def] >>
  drule_all target_subscript_target_well_formed >>
  fs[env_consistent_def, env_context_consistent_def]
QED

Theorem target_subscript_marked_nonhalted[local]:
  gas_marked_exec memory (ctx,func) source (es,s0) marks res mid (OK t) ==>
  ~t.vs_halted
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  drule gas_marked_path_exec >> strip_tac >> metis_tac[gas_path_normal]
QED

Theorem target_subscript_continuation_core[local]:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) /\
  ((?s p s1. eval_base_place cx bt s = (INL p,s1)) ==>
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_vv_case nocalls ctx func cenv cx e) /\
  (((!nsid. target_root bt = TopLevelNameTarget nsid ==>
      EVERY pure_expr (target_indices (SubscriptTarget bt e))) /\
    (!id. target_root bt = NameTarget id ==>
      ~supported_target_exists (\x. ?ty t. x = Pop ty t) (SubscriptTarget bt e))) \/
   (?id. !gs key ee.
     bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) = (INL key,ee) ==>
     ?path entry v. pv = PlaceR (MemoryPlace id path) /\
       lookup_scopes id ee.scopes = SOME entry /\
       evaluate_subscripts entry.type entry.value path = INL v)) /\
  type_place_target env bt = SOME bvt /\
  subscript_vtype bvt (expr_type e) = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  gas_marked_exec F (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) /\
  target_post ctx func cenv cx es sa sm s0 (mid with gas_obs := []) pv bvt rb t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\key. extend_place cx pv (ValueSubscript key)))
    (mid with gas_obs := [],t)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim ctx func cenv cx (expr_type e) e (mid with gas_obs := []) /\
   expr_vv_sim ctx func cenv cx (expr_type e) e (mid with gas_obs := [])` by
    (irule target_subscript_marked_index_sim >> goal_assum (drule_at Any) >>
     qexistsl [`env`, `nocalls`] >> simp[] >> first_assum ACCEPT_TAC) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
    (mid with gas_obs := [])` by
    (irule target_subscript_index_admissible >> goal_assum (drule_at Any) >> simp[]) >>
  `!gs v ee. bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := gs) = (INL v,ee) ==>
    place_readable cx ee pv` by
    (qpat_x_assum `_ \/ _` strip_assume_tac
     >- (`place_readable cx (mid with gas_obs := []) pv` by fs[target_post_def] >>
         rpt gen_tac >> strip_tac >>
         drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)
           target_subscript_marked_index_readable >>
         disch_then (qspec_then `e` irule) >> simp[] >>
         goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >>
         simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[] >>
     irule place_readable_memory_live >> metis_tac[]) >>
  `expr_sim_inv cenv cx env es` by fs[target_pre_def] >>
  `!l. FST rb <> Label l` by
    (drule_all target_subscript_typed_base_not_label >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule target_subscript_marked_base_domains >> simp[]) >>
  `~t.vs_halted` by metis_tac[target_subscript_marked_base_nonhalted] >>
  `gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (mid with gas_obs := [],t)
    (\res ee u. ?key. res = INL key /\
      target_post ctx func cenv cx es sa sn s0 ee pv bvt rb u /\
      expr_post ctx func cenv cx e (mid with gas_obs := []) sm sn t ee key ix u /\
      u.vs_current_bb = sn.cs_current_bb /\
      u.vs_inst_idx = LENGTH sn.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (irule target_index_outcome >> goal_assum (drule_at Any) >>
     gvs[ci_mono_def] >> first_assum ACCEPT_TAC) >>
  irule target_subscript_index_bind_outcome >>
  qexists `\key ee u.
    target_post ctx func cenv cx es sa sn s0 ee pv bvt rb u /\
    expr_post ctx func cenv cx e (mid with gas_obs := []) sm sn t ee key ix u /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts` >>
  pure_rewrite_tac[BETA_THM] >> reverse conj_tac >- (gvs[] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(\key ee u. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  `bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := gas_explicit right t.vs_gas_readings) =
    (INL key, ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule target_subscript_marked_base_source >>
  disch_then (qspec_then `gas_explicit right t.vs_gas_readings` assume_tac) >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `expr_sim_inv cenv cx env (mid with gas_obs := gas_explicit right t.vs_gas_readings)` by
    (drule_at (Pat `eval_base_place _ _ _ = _`) eval_base_place_sim_inv >>
     simp[]) >>
  `expr_body_pre cenv cx env e (mid with gas_obs := gas_explicit right t.vs_gas_readings)` by
    fs[target_pre_def, target_indices_pre_def] >>
  drule_all target_subscript_index_source_diagnostic >> strip_tac >>
  drule_all target_subscript_index_runtime_diagnostic >> strip_tac >>
  `(!id path. pv = PlaceR (MemoryPlace id path) ==>
      ?entry av. lookup_scopes id (ee with gas_obs := []).scopes = SOME entry /\
        evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
   (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
      storage_read_live cx tr (get_storage cx (ee with gas_obs := []) tr) slot tv /\
      w2n slot + type_slot_size tv <= dimword(:256) /\
      (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
        w2n (lookup_storage slot (get_storage cx (ee with gas_obs := []) tr)) <= cnt))` by
    (qpat_x_assum `_ \/ _` strip_assume_tac
     >- (drule_at (Pat `eval_base_place _ _ _ = _`) target_subscript_source_readiness >>
         simp[] >> disch_then drule_all >> simp[]) >>
     qpat_x_assum `!gs key ee. _` drule >> strip_tac >> gvs[] >>
     `?av. v = ArrayV av` by
       (irule target_subscript_memory_array_ready >>
        goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
        simp[] >> metis_tac[]) >> gvs[]) >>
  `local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV) bop_marked_scopes_dom) >> simp[]) >>
  drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    target_subscript_typed_summary >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then irule >> simp[] >>
  `?env'. expr_sim_inv cenv cx env' ee` by (qexists `env` >> fs[]) >>
  `!x. ix = Var x ==> not_fresh_at sn x` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `!x. FST op = Var x ==> not_fresh_at sb x` by
    (drule target_subscript_suffix_var >> simp[]) >>
  `~u.vs_halted` by (drule target_subscript_marked_nonhalted >> simp[]) >>
  `well_formed_vtype (get_tenv cx) vt` by
    (`well_formed_vtype (get_tenv cx) bvt` by
       metis_tac[target_subscript_pre_result_well_formed] >>
     metis_tac[target_subscript_vtype_well_formed]) >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  irule lower_compile_expr_not_label >>
  goal_assum (drule_at (Pat `lower_value`)) >>
  qexists_tac `env` >> fs[expr_body_pre_def, expr_sim_inv_def]
QED

Theorem target_subscript_base_continuation:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) /\
  ((?s p s1. eval_base_place cx bt s = (INL p,s1)) ==>
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_vv_case nocalls ctx func cenv cx e) /\
  (!nsid. target_root bt = TopLevelNameTarget nsid ==>
    EVERY pure_expr (target_indices (SubscriptTarget bt e))) /\
  (!id. target_root bt = NameTarget id ==>
    ~supported_target_exists (\x. ?ty t. x = Pop ty t) (SubscriptTarget bt e)) /\
  type_place_target env bt = SOME bvt /\
  subscript_vtype bvt (expr_type e) = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  gas_marked_exec F (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) /\
  target_post ctx func cenv cx es sa sm s0 (mid with gas_obs := []) pv bvt rb t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\key. extend_place cx pv (ValueSubscript key)))
    (mid with gas_obs := [],t)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  drule_at (Pat `target_pre _ _ _ _ _`) target_subscript_continuation_core >>
  disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  disch_then irule >> simp[] >> metis_tac[]
QED

(* target_subscript_base_continuation for a local root whose indices may
   pop, when every successful run of the index (for any gas observations)
   leaves the base's place live in the local's value: x[y.pop()] = v, or a
   pop that leaves the base's element in place.  The local's memory still
   holds the place (locals_kept, local_ptrs_rel), so the base's pointer
   reads what the source reads. *)
Theorem target_subscript_local_live_continuation:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) /\
  ((?s p s1. eval_base_place cx bt s = (INL p,s1)) ==>
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_vv_case nocalls ctx func cenv cx e) /\
  target_root bt = NameTarget id /\
  type_place_target env bt = SOME bvt /\
  subscript_vtype bvt (expr_type e) = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  gas_marked_exec F (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) /\
  target_post ctx func cenv cx es sa sm s0 (mid with gas_obs := []) pv bvt rb t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!gs key ee. bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) =
     (INL key,ee) ==>
     ?path entry v. pv = PlaceR (MemoryPlace id path) /\
       lookup_scopes id ee.scopes = SOME entry /\
       evaluate_subscripts entry.type entry.value path = INL v) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\key. extend_place cx pv (ValueSubscript key)))
    (mid with gas_obs := [],t)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  drule_at (Pat `target_pre _ _ _ _ _`) target_subscript_continuation_core >>
  disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  disch_then irule >> simp[] >> metis_tac[]
QED

(* RESIDUAL (self-overlap): a run of the index pops the base's own place
   out of the local's value, so the target overlaps its own index.
   Upstream rejects such targets (CompilerPanic "risky overlap"), so this
   stays admitted for the target read/write overlap exclusion. *)
Theorem target_subscript_local_popped_case:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) /\
  ((?s p s1. eval_base_place cx bt s = (INL p,s1)) ==>
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_vv_case nocalls ctx func cenv cx e) /\
  target_root bt = NameTarget id /\
  type_place_target env bt = SOME bvt /\
  subscript_vtype bvt (expr_type e) = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  gas_marked_exec F (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) /\
  target_post ctx func cenv cx es sa sm s0 (mid with gas_obs := []) pv bvt rb t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) =
    (INL key0,fin) /\
  ~(?path entry v. pv = PlaceR (MemoryPlace id path) /\
      lookup_scopes id fin.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\key. extend_place cx pv (ValueSubscript key)))
    (mid with gas_obs := [],t)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  cheat
QED

(* target_subscript_base_continuation for a local root whose indices may
   pop: split on whether the base's place is still live after the index. *)
Theorem target_subscript_local_pop_continuation:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) /\
  ((?s p s1. eval_base_place cx bt s = (INL p,s1)) ==>
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_vv_case nocalls ctx func cenv cx e) /\
  target_root bt = NameTarget id /\
  type_place_target env bt = SOME bvt /\
  subscript_vtype bvt (expr_type e) = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
  target_subscript_suffix cenv e rb ix sn = (op,sb) /\
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  gas_marked_exec F (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) /\
  target_post ctx func cenv cx es sa sm s0 (mid with gas_obs := []) pv bvt rb t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\key. extend_place cx pv (ValueSubscript key)))
    (mid with gas_obs := [],t)
    (\res ee u. ?pv'. res = INL pv' /\
      target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  Cases_on `!gs key ee.
    bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) =
      (INL key,ee) ==>
    ?path entry v. pv = PlaceR (MemoryPlace id path) /\
      lookup_scopes id ee.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v`
  >- (drule_all target_subscript_local_live_continuation >> simp[]) >>
  pop_assum (strip_assume_tac o SIMP_RULE pure_ss [NOT_FORALL_THM, NOT_IMP]) >>
  drule_all target_subscript_local_popped_case >> simp[]
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
  rpt gen_tac >> strip_tac >>
  rewrite_tac[target_case_def, target_sim_def] >> rpt strip_tac >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    metis_tac[target_subscript_base_admissible] >>
  `?bvt. type_place_target env bt = SOME bvt /\
          subscript_vtype bvt (expr_type e) = SOME vt` by
    fs[type_place_target_SubscriptTarget] >>
  drule target_subscript_compile_decompose >> strip_tac >>
  drule_all target_subscript_compile_intervals >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
   fn_has_code sn sb func` by
    (irule target_subscript_interval_code >> simp[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
    (\res ee t. ?pv. res = INL pv /\
      target_post ctx func cenv cx es sa sm s0 ee pv bvt rb t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (qpat_x_assum `target_case _ _ _ _ _ _` mp_tac >>
     simp[target_case_def, target_sim_def] >>
     disch_then (qspecl_then [`env`, `es`] mp_tac) >>
     impl_tac >- fs[int_calls_expr_def] >>
     disch_then irule >> simp[]) >>
  irule target_subscript_bind_outcome >>
  qexists `\pv ee t. target_post ctx func cenv cx es sa sm s0 ee pv bvt rb t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[BETA_THM] >>
  irule target_subscript_base_continuation >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl [`env`, `ix`, `nocalls`, `sn`] >> simp[] >> first_assum ACCEPT_TAC
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
  rpt gen_tac >> strip_tac >>
  rewrite_tac[target_case_def, target_sim_def] >> rpt strip_tac >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    metis_tac[target_subscript_base_admissible] >>
  `?bvt. type_place_target env bt = SOME bvt /\
          subscript_vtype bvt (expr_type e) = SOME vt` by
    fs[type_place_target_SubscriptTarget] >>
  drule target_subscript_compile_decompose >> strip_tac >>
  drule_all target_subscript_compile_intervals >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
   fn_has_code sn sb func` by
    (irule target_subscript_interval_code >> simp[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
    (\res ee t. ?pv. res = INL pv /\
      target_post ctx func cenv cx es sa sm s0 ee pv bvt rb t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (qpat_x_assum `target_case _ _ _ _ _ _` mp_tac >>
     simp[target_case_def, target_sim_def] >>
     disch_then (qspecl_then [`env`, `es`] mp_tac) >>
     impl_tac >- fs[int_calls_expr_def] >>
     disch_then irule >> simp[]) >>
  irule target_subscript_bind_outcome >>
  qexists `\pv ee t. target_post ctx func cenv cx es sa sm s0 ee pv bvt rb t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[BETA_THM] >>
  irule target_subscript_local_pop_continuation >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl [`env`, `id`, `ix`, `nocalls`, `sn`] >> simp[] >> first_assum ACCEPT_TAC
QED
