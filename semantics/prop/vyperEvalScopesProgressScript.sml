Theory vyperEvalScopesProgress
Ancestors
  pair sum vyperMisc vyperContext vyperState vyperCreate vyperCreateFrame vyperInterpreter vyperLookup
  vyperScopePreservation vyperStatePreservation vyperPlaceFrames vyperCallFrame vyperCallOutcomeFrame
  vyperCallOutcome[ignore_grammar] vyperEvalExprPreservesScopesDom

(* Every local of sc that sc' still has is unchanged in sc' or has more
   popped history.  Within an expression the only write to a local is a
   memory pop, which records one entry in the local's popped history
   (record_pop conses; replace_popped keeps the history's length); an
   internal call runs the callee in its own scopes and restores the
   caller's.  So a local whose entry is the same at both ends of an
   evaluation is the same at every point in between: the relation is
   transitive. *)
Definition scopes_progress_def:
  scopes_progress sc sc' <=>
    !n e e'. lookup_scopes n sc = SOME e /\ lookup_scopes n sc' = SOME e' ==>
             e' = e \/ LENGTH e.popped < LENGTH e'.popped
End

Theorem scopes_progress_refl[simp]:
  scopes_progress sc sc
Proof
  rw[scopes_progress_def] >> gvs[]
QED

Theorem lookup_scopes_dom_some[local]:
  !sc1 sc2 n e. MAP FDOM sc1 = MAP FDOM sc2 /\ lookup_scopes n sc1 = SOME e ==>
    ?e2. lookup_scopes n sc2 = SOME e2
Proof
  Induct >> Cases_on `sc2` >> simp[lookup_scopes_def] >> rpt gen_tac >>
  strip_tac >> Cases_on `FLOOKUP h' n` >> gvs[AllCaseEqs()] >>
  gvs[finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]
QED

Theorem scopes_progress_trans:
  MAP FDOM sc1 = MAP FDOM sc2 /\
  scopes_progress sc1 sc2 /\ scopes_progress sc2 sc3 ==> scopes_progress sc1 sc3
Proof
  rw[scopes_progress_def] >>
  drule_all lookup_scopes_dom_some >> strip_tac >>
  rpt (first_x_assum drule_all >> strip_tac) >> gvs[]
QED

Theorem replace_popped_length[local]:
  !history tv path replacement history'.
    replace_popped tv path replacement history = SOME history' ==>
    LENGTH history' = LENGTH history
Proof
  Induct >> simp[Once replace_popped_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[Once replace_popped_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

Theorem scopes_progress_update:
  find_containing_scope id sc = SOME (pre,env,entry,rest) /\
  (entry' = entry \/ LENGTH entry.popped < LENGTH entry'.popped) ==>
  scopes_progress sc (pre ++ (env |+ (id,entry'))::rest)
Proof
  strip_tac >>
  drule find_containing_scope_lookup >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  rw[scopes_progress_def] >> Cases_on `n = id` >>
  gvs[lookup_scopes_update, lookup_scopes_update_other] >> metis_tac[]
QED

Theorem pop_place_scopes_progress[local]:
  pop_place cx p st = (res,st') ==> scopes_progress st.scopes st'.scopes
Proof
  Cases_on `p`
  >- metis_tac[pop_storage_place_scopes_immutables, scopes_progress_refl]
  >- (rename1 `MemoryPlace id path` >> strip_tac >>
      Cases_on `find_containing_scope id st.scopes` >>
      gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
          return_def, raise_def] >> PairCases_on `x` >>
      gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
          check_def, set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
      fs[GSYM lift_sum_def, GSYM lift_option_type_def] >>
      imp_res_tac lift_sum_state >> imp_res_tac lift_option_type_state >> gvs[] >>
      pairarg_tac >> gvs[bind_def, ignore_bind_def, set_scopes_def, return_def] >>
      irule scopes_progress_update >> goal_assum (drule_at Any) >>
      gvs[lift_option_type_def, lift_sum_def, sum_CASE_rator, option_CASE_rator,
          return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac replace_popped_length >> simp[record_pop_def]) >>
  simp[pop_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, ignore_bind_def,
           lift_option_type_def, lift_sum_def, get_immutables_def,
           get_address_immutables_def, return_def, raise_def]) >>
  metis_tac[set_immutable_scopes, scopes_progress_refl]
QED

Theorem finally_set_scopes_then_scopes[local]:
  finally f (bind (set_scopes prev) k) st = (res,st') ==>
  (!s r t. k () s = (r,t) ==> t.scopes = s.scopes) ==>
  st'.scopes = prev
Proof
  rpt strip_tac >>
  fs[finally_def, AllCaseEqs(), ignore_bind_def, bind_def,
     set_scopes_def, return_def, raise_def] >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem eval_mutual_scopes_progress[local]:
  (!cx:evaluation_context. !s:stmt. T) /\
  (!cx:evaluation_context. !ss:stmt list. T) /\
  (!cx:evaluation_context. !it:iterator. T) /\
  (!cx:evaluation_context. !tv:type_value. !id:string. !body:stmt list. !vs:value list. T) /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==>
    scopes_progress st.scopes st'.scopes) /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==>
    scopes_progress st.scopes st'.scopes) /\
  (!cx bt st res st'. eval_base_place cx bt st = (res,st') ==>
    scopes_progress st.scopes st'.scopes) /\
  (!cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
    scopes_progress st.scopes st'.scopes) /\
  (!cx:evaluation_context. !g:assignment_target. !v:value. T) /\
  (!cx:evaluation_context. !gs:assignment_target list. !vs:value list. T) /\
  (!cx es st res st'. eval_expr_results cx es st = (res,st') ==>
    scopes_progress st.scopes st'.scopes)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, lift_option_type_def, return_def,
          raise_def, AllCaseEqs()])
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac lookup_global_scopes >> gvs[])
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac lookup_flag_mem_scopes >> gvs[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def,
          switch_BoolV_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac read_result_state >>
      imp_res_tac conditional_result_state >> gvs[] >>
      gvs[COND_RATOR, AllCaseEqs(), raise_def] >>
      imp_res_tac eval_expr_preserves_scopes_dom >>
      metis_tac[scopes_progress_trans])
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac read_result_state >> imp_res_tac select_result_state >>
      gvs[] >> imp_res_tac eval_expr_preserves_scopes_dom >>
      metis_tac[scopes_progress_trans])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac select_result_state >> gvs[] >> metis_tac[])
  >- suspend "Builtin"
  >- (rpt strip_tac >>
      qpat_x_assum `eval_expr cx (Pop _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      strip_tac >> imp_res_tac pop_place_scopes_progress >>
      imp_res_tac eval_target_place_preserves_scopes_dom >>
      metis_tac[scopes_progress_trans])
  >- suspend "TypeBuiltin"
  >- suspend "Send"
  >- suspend "ExtCall"
  >- suspend "IntCall"
  >- suspend "RawCall"
  >- suspend "RawCall2"
  >- suspend "Log"
  >- suspend "PureCall"
  >- suspend "Transfer"
  >- suspend "CreateTarget"
  >- simp[Once evaluate_def, return_def]
  >- (rpt strip_tac >>
      qpat_x_assum `eval_exprs cx (_::_) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      strip_tac >> imp_res_tac read_result_state >> gvs[] >>
      imp_res_tac eval_expr_preserves_scopes_dom >>
      metis_tac[scopes_progress_trans])
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
      imp_res_tac read_result_state >> imp_res_tac extend_place_state >> gvs[] >>
      imp_res_tac eval_base_place_preserves_scopes_dom >>
      metis_tac[scopes_progress_trans])
  >- (rpt strip_tac >>
      qpat_x_assum `eval_target_place cx _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac get_place_state >> gvs[] >> metis_tac[])
  >- simp[Once evaluate_def, return_def]
  >> rpt strip_tac >>
  qpat_x_assum `eval_expr_results cx (_::_) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> imp_res_tac eval_expr_preserves_scopes_dom >>
  metis_tac[scopes_progress_trans]
QED

Resume eval_mutual_scopes_progress[Builtin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (Cases_on `bt = Len` >> rpt gen_tac >> strip_tac >>
      Cases_on `bt = Env MsgGas` >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, AllCaseEqs()] >>
      imp_res_tac result_array_length_state >>
      imp_res_tac next_gas_reading_state >>
      imp_res_tac precompile_call_success_state >>
      imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >> gvs[] >>
      first_x_assum drule >> simp[type_check_def, assert_def, return_def] >>
      metis_tac[])
  >> simp[Once evaluate_def, type_check_def, assert_def, bind_def,
          ignore_bind_def, raise_def]
QED

Resume eval_mutual_scopes_progress[TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `type_builtin_args_length_ok tb (LENGTH es)` >>
  rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >>
  first_x_assum drule >> simp[type_check_def, assert_def, return_def]
QED

Resume eval_mutual_scopes_progress[Send]:
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

Resume eval_mutual_scopes_progress[ExtCall]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr cx (Call _ (ExtCall _ _ _ _) _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> imp_res_tac eval_ext_call_preserves_non_accounts >>
  imp_res_tac read_results_state >> gvs[] >>
  rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!a b c. _` drule_all >> strip_tac) >>
  imp_res_tac eval_exprs_preserves_scopes_dom >>
  imp_res_tac eval_expr_results_preserves_scopes_dom >>
  metis_tac[scopes_progress_trans]
QED

Resume eval_mutual_scopes_progress[RawCall]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, type_check_def, assert_def, lift_option_type_def,
       option_CASE_rator] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[]
QED

Resume eval_mutual_scopes_progress[RawCall2]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, type_check_def, assert_def, lift_option_type_def,
       option_CASE_rator] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[]
QED

Resume eval_mutual_scopes_progress[Log]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, check_def, type_check_def, assert_def, lift_option_def,
       lift_option_type_def, push_log_def, option_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >> metis_tac[]
QED

Resume eval_mutual_scopes_progress[PureCall]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
      raise_def, check_def, type_check_def, assert_def] >> metis_tac[]
QED

Resume eval_mutual_scopes_progress[Transfer]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, check_def, type_check_def, assert_def, lift_option_def,
       lift_option_type_def, get_accounts_def, option_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac transfer_value_scopes >> gvs[] >> metis_tac[]
QED

Resume eval_mutual_scopes_progress[CreateTarget]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `kind` >> gvs[] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  imp_res_tac check_create_blueprint_result_state >> gvs[] >>
  imp_res_tac read_results_state >> gvs[] >>
  rpt (qpat_x_assum `!a b c d e f. _` drule_all >> strip_tac) >>
  rpt (qpat_x_assum `!st res st'. _` drule_all >> strip_tac) >>
  imp_res_tac eval_create_preserves_scopes_immutables >> gvs[] >>
  imp_res_tac eval_expr_preserves_scopes_dom >>
  imp_res_tac eval_exprs_preserves_scopes_dom >>
  imp_res_tac eval_expr_results_preserves_scopes_dom >>
  irule scopes_progress_trans >> goal_assum (drule_at Any) >> simp[] >>
  irule scopes_progress_trans >> goal_assum (drule_at Any) >> simp[]
QED

Resume eval_mutual_scopes_progress[IntCall]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum
    `!s t s1 ts t1 s2 tup t2 s3 t3. _ ==>
       !st res st'. eval_expr_results cx es st = (res,st') ==> _`
    (mp_tac o SRULE [type_check_def, assert_def, lift_option_type_def,
                     option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  disch_then assume_tac >>
  qpat_x_assum
    `!s t s1 ts t1 s2 tup t2 s3 t3 s4 vs t4 s5 prev t5 s6 t6. _` kall_tac >>
  rpt gen_tac >> rewrite_tac[Once evaluate_def] >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (drule type_check_scopes >> rw[] >> gvs[]) >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (imp_res_tac type_check_scopes >> imp_res_tac lift_option_type_scopes >>
      rw[] >> gvs[]) >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (imp_res_tac type_check_scopes >> imp_res_tac lift_option_type_scopes >>
      rw[] >> gvs[]) >>
  BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum `_ r' = (res,st')` mp_tac >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (imp_res_tac type_check_scopes >> imp_res_tac lift_option_type_scopes >>
      rw[] >> gvs[]) >>
  unabbrev_all_tac >>
  rule_assum_tac (SRULE [type_check_def, assert_def, lift_option_type_def,
                        option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  gvs[] >> BasicProvers.TOP_CASE_TAC >>
  first_x_assum drule >> strip_tac >> reverse (Cases_on `q`)
  >- (rw[] >> gvs[]) >>
  simp[bind_def, ignore_bind_def, get_scopes_def, return_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> drule finally_set_scopes >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> imp_res_tac finally_set_scopes >>
  qpat_x_assum `_ = (res,st')` mp_tac >>
  simp[pop_function_def, push_function_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac lift_option_type_scopes >>
  imp_res_tac read_results_state >>
  TRY (drule finally_set_scopes_then_scopes >>
       (impl_tac
        >- (rpt gen_tac >> Cases_on `cx.nonreentrant_slot` >>
            simp[COND_RATOR, option_CASE_rator, AllCaseEqs(), return_def] >>
            rpt strip_tac >> imp_res_tac release_nonreentrant_lock_scopes >> gvs[])) >>
       strip_tac >> gvs[] >> NO_TAC) >>
  gvs[] >>
  Cases_on `FST (SND x'')` >> Cases_on `cx.nonreentrant_slot` >>
  gvs[bind_def, ignore_bind_def, COND_RATOR, AllCaseEqs(),
      return_def, raise_def, check_not_static_def, check_def, assert_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >> gvs[]
QED

Finalise eval_mutual_scopes_progress

Theorem eval_scopes_progress:
  (!cx e st res st'. eval_expr cx e st = (res,st') ==>
     scopes_progress st.scopes st'.scopes) /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==>
     scopes_progress st.scopes st'.scopes) /\
  (!cx bt st res st'. eval_base_place cx bt st = (res,st') ==>
     scopes_progress st.scopes st'.scopes) /\
  (!cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
     scopes_progress st.scopes st'.scopes) /\
  (!cx es st res st'. eval_expr_results cx es st = (res,st') ==>
     scopes_progress st.scopes st'.scopes)
Proof
  metis_tac[eval_mutual_scopes_progress]
QED
