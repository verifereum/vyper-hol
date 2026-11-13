(* Forward selected-prefix interfaces for internal-call defaults and body.
 * The selected trace and initial state remain fixed across stack changes. *)
Theory guardSourceIntCall
Ancestors
  guardSourceInstrumentation vyperFiniteStoragePreservation
  vyperStorageFootprint guardSourceOrdinarySchema vyperTypeSystem
  vyperTypeCallGraph vyperInterpreter vyperState vyperTypeEvalSoundness
  vyperTypeCallStackSoundness vyperEvalMisc vyperStorageTrace
Libs
  guardSourceSchemaLib

Theorem valid_horizon_stk[local]:
  valid_horizon (cx with stk updated_by f) initial_st H tr <=>
  valid_horizon cx initial_st H tr
Proof
  simp[valid_horizon_def, storage_well_formed_on_stk,
       storage_observations_ok_stk]
QED

Theorem default_finally_finite_prefix[local]:
  (!r t.
    eval_exprs cxd ds (st with scopes := [FEMPTY]) = (r,t) /\
    (?sfx. selected = t.storage_trace ++ sfx) ==>
    storage_well_formed_on cxd t (FST H) /\
    storage_observations_ok cxd H t.storage_trace) /\
  finally (do set_scopes [FEMPTY]; eval_exprs cxd ds od)
    (set_scopes st.scopes) st = (res,out) /\
  (?sfx. selected = out.storage_trace ++ sfx) ==>
  storage_well_formed_on cxd out (FST H) /\
  storage_observations_ok cxd H out.storage_trace
Proof
  strip_tac >> drule default_finally_result >> strip_tac >> gvs[] >>
  simp[storage_well_formed_on_scopes]
QED

Theorem finite_prefix_Expr_Call_IntCall:
  ^(guardSourceSchemaLib.branch
      guardSourceOrdinarySchemaTheory.finite_prefix_evaluate_ind
      "Expr_Call_IntCall")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ (IntCall _) _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (irule call_evaluation_safe_mono >>
     goal_assum (drule_at Any) >> simp[int_calls_expr_def]) >>
  qpat_x_assum `well_typed_expr env (Call _ (IntCall _) _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[Once evaluate_def] >>
  simp_tac std_ss [Once ignore_bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac vyperStatePreservationTheory.type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >>
      gvs[type_check_def, assert_def, valid_horizon_def]) >>
  simp_tac std_ss [Once bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac vyperStatePreservationTheory.lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >>
      gvs[valid_horizon_def]) >>
  simp_tac std_ss [Once bind_apply, LET_THM] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac vyperStatePreservationTheory.lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >>
      gvs[valid_horizon_def]) >>
  simp_tac std_ss [Once ignore_bind_apply, LET_THM] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac vyperStatePreservationTheory.type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >>
      gvs[valid_horizon_def]) >>
  simp_tac std_ss [Once bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  qmatch_asmsub_rename_tac `eval_expr_results cx es st = (args_res,args_st)` >>
  Cases_on `args_res` >> simp_tac std_ss [] >> strip_tac
  >- (qmatch_asmsub_abbrev_tac `kont args_st = (res,st')` >>
      `storage_trace_frame kont` by
        (unabbrev_all_tac >>
         rpt (FIRST [
           irule storage_trace_frame_bind_all >> conj_tac,
           irule storage_trace_frame_ignore_bind >> conj_tac,
           irule storage_trace_frame_finally >> conj_tac,
           irule storage_trace_frame_finally_unless_halt >> conj_tac,
           irule storage_trace_frame_try >> conj_tac,
           gen_tac,
           CHANGED_TAC (simp_tac std_ss
             [storage_trace_frame_return, storage_trace_frame_lifts,
              storage_trace_frame_state_reads, storage_trace_frame_state_updates,
              storage_trace_frame_read_results, storage_trace_frame_optional_locks,
              storage_trace_frame_function_stack, storage_trace_frame_function_handler,
              evaluate_storage_trace_frame])])) >>
      `?tail. selected = args_st.storage_trace ++ tail` by
        (drule_all storage_trace_frame_prefix >> strip_tac >>
         metis_tac[listTheory.APPEND_ASSOC]) >>
      qpat_x_assum `!s0 x0 t0 s1 ts t1 s2 tup t2 mut stup nr stup2 args sstup dflts sstup2 ret body s3 x3 t3. _`
        (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      disch_then drule >> disch_then drule >>
      simp_tac std_ss [] >>
      disch_then (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      disch_then (assume_tac o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      `storage_well_formed_on cx args_st (FST H) /\
       storage_observations_ok cx H args_st.storage_trace` by
        (first_x_assum (irule o PURE_REWRITE_RULE [AND_IMP_INTRO]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qmatch_asmsub_rename_tac `eval_expr_results cx es st = (INL args_vals,args_st)` >>
         qexistsl [`env`, `initial_st`, `INL args_vals`, `selected`, `st`] >>
         conj_tac >- metis_tac[] >>
         conj_tac >- (qexists_tac `tail` >> first_assum ACCEPT_TAC) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      first_x_assum (drule_at (Pat `type_check _ "recursion" _ = _`)) >>
      disch_then (drule_at (Pat `lift_option_type (get_module_code _ _) _ _ = _`)) >>
      disch_then (drule_at (Pat `lift_option_type (lookup_callable_function _ _ _) _ _ = _`)) >>
      simp_tac std_ss [] >>
      disch_then (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      disch_then (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      disch_then (assume_tac o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      first_x_assum (drule_at (Pat `type_check _ "recursion" _ = _`)) >>
      disch_then (drule_at (Pat `lift_option_type (get_module_code _ _) _ _ = _`)) >>
      disch_then (drule_at (Pat `lift_option_type (lookup_callable_function _ _ _) _ _ = _`)) >>
      simp_tac std_ss [] >>
      disch_then (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      disch_then (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      disch_then (assume_tac o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      qpat_assum `runtime_consistent env cx st`
        (strip_assume_tac o SRULE [vyperTypeExprSoundnessTheory.runtime_consistent_def]) >>
      drule_all (cj 1 (cj 11 eval_scc_type_sound_results_mutual)) >> strip_tac >>
      qpat_assum `lift_option_type (get_module_code cx _) _ _ = _`
        (strip_assume_tac o SRULE [lift_option_type_def, vyperMiscTheory.option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
      qpat_assum `lift_option_type (lookup_callable_function _ _ _) _ _ = _`
        (strip_assume_tac o SRULE [lift_option_type_def, vyperMiscTheory.option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
      qmatch_asmsub_rename_tac `lookup_callable_function _ _ _ = SOME callable` >>
      PairCases_on `callable` >>
      `IS_SOME (FLOOKUP env.fn_sigs (src_id_opt,fn))` by simp[] >>
      drule_all callable_body_typing_from_env_consistent >>
      disch_then (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `env_body` (qx_choose_then `ret_tv`
          (qx_choose_then `env_after` (fn th => map_every assume_tac (CONJUNCTS th)))))) >>
      drule_all intcall_default_env_side_conditions >>
      disch_then (qspec_then `fn` strip_assume_tac) >>
      `runtime_consistent (defaults_env env_body)
         (cx with stk updated_by CONS (src_id_opt,fn))
         (args_st with scopes := [FEMPTY])` by
        (simp[vyperTypeExprSoundnessTheory.runtime_consistent_def] >> conj_tac
         >- (irule defaults_env_empty_frame_consistent >> simp[]) >>
         qpat_assum `state_well_typed args_st` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[vyperTypeInvariantsTheory.state_well_typed_def,
              vyperTypeInvariantsTheory.scope_well_typed_def]) >>
      `call_evaluation_safe (cx with stk updated_by CONS (src_id_opt,fn))
        (int_calls_exprs (DROP (LENGTH callable3 - (LENGTH callable2 - LENGTH es)) callable3))` by
        (qpat_assum `get_module_code _ _ = SOME _` mp_tac >>
         qpat_assum `lookup_callable_function _ _ _ = SOME _` mp_tac >>
         qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[int_calls_expr_def] >> rpt strip_tac >>
         irule call_evaluation_safe_push_needed_defaults >> metis_tac[]) >>
      `well_typed_exprs (defaults_env env_body)
        (DROP (LENGTH callable3 - (LENGTH callable2 - LENGTH es)) callable3)` by
        (irule well_typed_exprs_DROP >> simp[]) >>
      qpat_x_assum `kont args_st = _` mp_tac >>
      simp_tac std_ss [Abbr `kont`, Once bind_apply, get_scopes_def, return_def] >>
      simp_tac std_ss [pairTheory.pair_case_thm] >>
      simp_tac std_ss [Once bind_apply] >>
      BasicProvers.TOP_CASE_TAC >>
      qmatch_asmsub_rename_tac `finally _ _ args_st = (defaults_res,defaults_st)` >>
      `get_scopes args_st = (INL args_st.scopes,args_st)` by
        simp[get_scopes_def,return_def] >>
      qpat_x_assum `!needed_dflts cxd s0 prev t0 s1 x0 t1. _`
        (mp_tac o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      simp_tac std_ss [] >>
      disch_then drule >>
      disch_then assume_tac >>
      `set_scopes [FEMPTY] args_st = (INL (),args_st with scopes := [FEMPTY])` by
        simp[set_scopes_def,return_def] >>
      qpat_x_assum `!s0 prev t0 s1 x0 t1 initial_st selected env st0 res st1. _`
        (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      disch_then drule >>
      disch_then (assume_tac o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      `(?sfx. selected = defaults_st.storage_trace ++ sfx) ==>
       storage_well_formed_on cx defaults_st (FST H) /\
       storage_observations_ok cx H defaults_st.storage_trace` by
        (strip_tac >>
         `storage_well_formed_on (cx with stk updated_by CONS (src_id_opt,fn)) defaults_st (FST H) /\
          storage_observations_ok (cx with stk updated_by CONS (src_id_opt,fn)) H defaults_st.storage_trace`
           suffices_by (pure_rewrite_tac [storage_well_formed_on_stk, storage_observations_ok_stk] >> simp_tac bool_ss []) >>
         irule default_finally_finite_prefix >>
         goal_assum (drule_at (Pat `finally _ _ _ = _`)) >>
         qexists_tac `selected` >>
         reverse conj_tac >- metis_tac[] >>
         rpt gen_tac >> strip_tac >>
         first_x_assum (irule o PURE_REWRITE_RULE [AND_IMP_INTRO]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl [`defaults_env env_body`, `initial_st`, `r`, `selected`,
                    `args_st with scopes := [FEMPTY]`] >>
         conj_tac
         >- (pure_rewrite_tac [valid_horizon_stk, storage_well_formed_on_stk] >> metis_tac[]) >>
         conj_tac >- metis_tac[] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac
         >- (simp_tac (srw_ss()) [] >>
             drule vyperEvalOutcomeSuffixTheory.eval_expr_results_outcome_suffix >>
             metis_tac[exprOracleStorageInterfacesTheory.outcome_suffix_IS_SOME]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- (pure_rewrite_tac [storage_well_formed_on_scopes, storage_well_formed_on_stk] >> first_assum ACCEPT_TAC) >>
         simp_tac (srw_ss()) [valid_horizon_stk, valid_horizon_def] >>
         metis_tac[valid_horizon_def]) >>
      reverse (Cases_on `defaults_res`) >> simp_tac std_ss []
      >- (disch_then (strip_assume_tac o PURE_REWRITE_RULE [pairTheory.PAIR_EQ]) >>
          BasicProvers.VAR_EQ_TAC >>
          qpat_x_assum `(?sfx. _ = _.storage_trace ++ sfx) ==> _` irule >>
          metis_tac[]) >>
      strip_tac >>
      qmatch_asmsub_abbrev_tac `body_kont defaults_st = (res,st')` >>
      `storage_trace_frame body_kont` by
        (unabbrev_all_tac >>
         rpt (FIRST [
           irule storage_trace_frame_bind_all >> conj_tac,
           irule storage_trace_frame_ignore_bind >> conj_tac,
           irule storage_trace_frame_finally >> conj_tac,
           irule storage_trace_frame_finally_unless_halt >> conj_tac,
           irule storage_trace_frame_try >> conj_tac,
           gen_tac,
           CHANGED_TAC (simp_tac std_ss
             [storage_trace_frame_return, storage_trace_frame_lifts,
              storage_trace_frame_state_reads, storage_trace_frame_state_updates,
              storage_trace_frame_read_results, storage_trace_frame_optional_locks,
              storage_trace_frame_function_stack, storage_trace_frame_function_handler,
              evaluate_storage_trace_frame])])) >>
      `?dtail. selected = defaults_st.storage_trace ++ dtail` by
        (drule_all storage_trace_frame_prefix >> strip_tac >>
         metis_tac[listTheory.APPEND_ASSOC]) >>
      qpat_x_assum `(?sfx. selected = defaults_st.storage_trace ++ sfx) ==> _` mp_tac >>
      impl_tac >- metis_tac[] >> strip_tac >>
      suspend "body_setup") >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!s0 x0 t0 s1 ts t1 s2 tup t2 mut stup nr stup2 args sstup dflts sstup2 ret body s3 x3 t3. _`
    (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then drule >> disch_then drule >>
  simp_tac std_ss [] >>
  disch_then (drule o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then (irule o PURE_REWRITE_RULE [AND_IMP_INTRO]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `eval_expr_results _ _ _ = _`)) >>
  qexistsl [`env`, `initial_st`, `selected`] >>
  rpt conj_tac >> metis_tac[]
QED

Resume finite_prefix_Expr_Call_IntCall[body_setup]:
  qpat_x_assum `body_kont defaults_st = _` mp_tac >>
  simp_tac std_ss [Abbr `body_kont`, Once bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac read_results_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (simp_tac std_ss [] >>
      disch_then (strip_assume_tac o PURE_REWRITE_RULE [pairTheory.PAIR_EQ]) >>
      BasicProvers.VAR_EQ_TAC >> conj_tac >> first_assum ACCEPT_TAC) >>
  simp_tac std_ss [Once bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
  BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (simp_tac std_ss [] >>
      disch_then (strip_assume_tac o PURE_REWRITE_RULE [pairTheory.PAIR_EQ]) >>
      BasicProvers.VAR_EQ_TAC >> conj_tac >> first_assum ACCEPT_TAC) >>
  `lift_option_type (evaluate_type (get_tenv cx) callable4) "IntCall eval ret" defaults_st =
     (INL ret_tv,defaults_st)` by
    (qpat_assum `evaluate_type _ _ = SOME ret_tv` (fn th =>
       simp_tac std_ss [th, lift_option_type_def, return_def])) >>
  qpat_x_assum `!s d t s1 vs t1 s2 env t2 s3 rtv t3 s4 x t4 s5 cxf t5 initial selected env1 ret env2 st1 res1 st2. _`
    (drule_at (Pat `finally _ _ _ = _`)) >>
  disch_then (drule_at (Pat `read_results _ _ _ = _`)) >>
  disch_then (drule_at (Pat `lift_option_type _ "IntCall bind_arguments" _ = _`)) >>
  disch_then (drule_at (Pat `lift_option_type _ "IntCall eval ret" _ = _`)) >>
  disch_then assume_tac >>
  simp_tac std_ss [Once bind_apply, lift_option_type_def, return_def, pairTheory.pair_case_thm] >>
  simp_tac std_ss [Once ignore_bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  qmatch_asmsub_rename_tac `lock_if_nr cx callable1 (is_view_mut callable0) defaults_st = (lock_res,lock_st)` >>
  reverse (Cases_on `lock_res`) >> simp_tac std_ss []
  >- suspend "lock_error" >>
  simp_tac std_ss [Once bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  simp_tac std_ss [pairTheory.pair_case_thm] >>
  strip_tac >> suspend "body_input"
QED

Resume finite_prefix_Expr_Call_IntCall[lock_error]:
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `lock_if_nr _ _ _ _ = _` mp_tac >>
  qpat_x_assum `storage_well_formed_on cx defaults_st (FST H)` mp_tac >>
  qpat_x_assum `storage_observations_ok cx H defaults_st.storage_trace` mp_tac >>
  qpat_x_assum `selected = st'.storage_trace ++ sfx` mp_tac >>
  qpat_x_assum `EVERY _ (storage_trace_locks selected)` mp_tac >>
  qpat_x_assum `storage_roots_fit selected` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  qpat_x_assum `lock_if_nr _ _ _ _ = _` mp_tac >>
  Cases_on `callable1` >>
  simp_tac (srw_ss()) [lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  simp_tac (srw_ss()) [raise_def, ignore_bind_def, bind_def,
    vyperTypeEvalStoragePreservationTheory.acquire_nonreentrant_lock_eq,
    return_def] >>
  rpt IF_CASES_TAC >>
  simp_tac (srw_ss()) [is_view_mut_def,
    check_not_static_eq,
    return_def] >> rpt strip_tac >> BasicProvers.VAR_EQ_TAC >>
  gvs[storage_observations_ok_append, storage_well_formed_on_def,
      vyperStorageBackendTheory.get_storage_def, storage_observations_ok_def, storage_trace_regions_def,
      storage_trace_locks_def, storage_roots_fit_def,
      storage_trace_backends_well_formed_def]
QED

Resume finite_prefix_Expr_Call_IntCall[body_input]:
  qpat_x_assum `push_function _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [push_function_def, return_def] >>
  disch_then (strip_assume_tac o PURE_REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `INL _ = q` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `(case INL _ of _ => _ | _ => _) = _` mp_tac >>
  simp_tac std_ss [] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `cleanup_kont (lock_st with scopes := [call_env]) = (res,st')` >>
  `storage_trace_frame cleanup_kont` by
    (unabbrev_all_tac >>
     rpt (FIRST [
       irule storage_trace_frame_bind_all >> conj_tac,
       irule storage_trace_frame_ignore_bind >> conj_tac,
       irule storage_trace_frame_finally >> conj_tac,
       irule storage_trace_frame_finally_unless_halt >> conj_tac,
       irule storage_trace_frame_try >> conj_tac,
       gen_tac,
       CHANGED_TAC (simp_tac std_ss
         [storage_trace_frame_return, storage_trace_frame_lifts,
          storage_trace_frame_state_reads, storage_trace_frame_state_updates,
          storage_trace_frame_optional_locks, storage_trace_frame_function_stack,
          storage_trace_frame_function_handler, evaluate_storage_trace_frame])]) >>
     Cases_on `safe_cast ret_tv v` >>
     simp_tac std_ss [storage_trace_frame_return, storage_trace_frame_raise]) >>
  `?ltail. selected = lock_st.storage_trace ++ ltail` by
    (drule_all storage_trace_frame_prefix >>
     simp_tac (srw_ss()) [] >> metis_tac[listTheory.APPEND_ASSOC]) >>
  suspend "lock_success"
QED

Resume finite_prefix_Expr_Call_IntCall[lock_success]:
  `storage_well_formed_on cx lock_st (FST H) /\
   storage_observations_ok cx H lock_st.storage_trace` by
    (qpat_x_assum `lock_if_nr _ _ _ _ = _` mp_tac >>
     qpat_x_assum `storage_well_formed_on cx defaults_st (FST H)` mp_tac >>
     qpat_x_assum `storage_observations_ok cx H defaults_st.storage_trace` mp_tac >>
     qpat_x_assum `selected = lock_st.storage_trace ++ ltail` mp_tac >>
     qpat_x_assum `EVERY _ (storage_trace_locks selected)` mp_tac >>
     qpat_x_assum `storage_roots_fit selected` mp_tac >>
     qpat_x_assum `regions_consistent (FST H)` mp_tac >>
     qpat_x_assum `storage_locks_separated (FST H) (SND H)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     qpat_x_assum `lock_if_nr _ _ _ _ = _` mp_tac >>
     Cases_on `callable1` >>
     simp_tac (srw_ss()) [lock_if_nr_def, return_def] >>
     Cases_on `cx.nonreentrant_slot` >>
     simp_tac (srw_ss()) [raise_def, ignore_bind_def, bind_def,
       vyperTypeEvalStoragePreservationTheory.acquire_nonreentrant_lock_eq,
       return_def] >>
     rpt IF_CASES_TAC >>
     simp_tac (srw_ss()) [is_view_mut_def, check_not_static_eq, return_def] >>
     rpt strip_tac >> BasicProvers.VAR_EQ_TAC >>
     gvs[storage_well_formed_on_def, vyperStorageBackendTheory.get_storage_def,
       storage_observations_ok_append, storage_observations_ok_def,
       storage_trace_regions_def, storage_trace_locks_def, storage_roots_fit_def,
       storage_trace_backends_well_formed_def] >>
     PURE_REWRITE_TAC [GSYM storage_well_formed_on_def] >>
     irule lock_frame_preserves_storage_well_formed_on >>
     conj_tac >- simp[] >>
     qexistsl [`x`,`SND H`,`defaults_st`] >>
     simp_tac (srw_ss()) [storage_well_formed_on_def] >>
     rpt strip_tac >>
     simp[vfmExecutionTheory.lookup_transient_storage_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       vfmExecutionTheory.update_transient_storage_def] >>
     Cases_on `addr = cx.txn.target` >> simp[combinTheory.APPLY_UPDATE_THM]) >>
  qpat_assum `case INL _ of INL results => expr_results_typed _ _ _ | INR _ => _`
    (assume_tac o SRULE []) >>
  drule read_results_state >> disch_then SUBST_ALL_TAC >>
  qpat_assum `lift_option_type _ "IntCall bind_arguments" _ = _`
    (mp_tac o MATCH_MP vyperStatePreservationTheory.lift_option_type_state) >>
  disch_then SUBST_ALL_TAC >>
  qpat_assum `lock_if_nr _ _ _ _ = (INL _,_)`
    (assume_tac o SRULE [pairTheory.FST, sumTheory.INL_11]) >>
  qmatch_asmsub_rename_tac `lock_if_nr cx callable1 (is_view_mut callable0) defaults_st = (INL lock_unit,lock_st)` >>
  Cases_on `lock_unit` >>
  `runtime_consistent env_body (cx with stk updated_by CONS (src_id_opt,fn))
     (lock_st with scopes := [call_env])` by
    (irule intcall_defaults_body_runtime >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     qpat_assum `finally _ _ args_st = _` (irule_at (Pat `finally _ _ _ = _`)) >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  qpat_x_assum `Abbrev (cleanup_kont = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  disch_then SUBST_ALL_TAC >>
  qpat_x_assum `(do rv <- _; _ od) _ = _` mp_tac >>
  simp_tac std_ss [Once bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  strip_tac >>
  qpat_assum `finally_unless_halt _ _ _ = _`
    (mp_tac o MATCH_MP finally_unless_halt_finite_cleanup_cases o
     REWRITE_RULE [unlock_if_nr_def]) >>
  disch_then (qx_choose_then `release` assume_tac) >>
  qpat_x_assum `finally_unless_halt _ _ _ = _` kall_tac >>
  qmatch_asmsub_rename_tac `finally _ _ _ = (final_res,final_st)` >>
  `st' = final_st` by
    (qpat_x_assum `finally _ _ _ = _` kall_tac >>
     qpat_x_assum `(case final_res of _ => _ | _ => _) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `final_res` >>
     simp_tac(srw_ss())[bind_def, return_def] >>
     Cases_on `safe_cast ret_tv x` >>
     simp_tac(srw_ss())[bind_def, return_def, raise_def] >>
     rpt strip_tac >> gvs[]) >>
  qpat_x_assum `st' = final_st` SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `finally handled cleanup body_input = _` >>
  Cases_on `handled body_input` >> rename1 `handled body_input = (hr,hs)` >>
  Cases_on `cleanup hs` >> rename1 `cleanup hs = (cr,cs)` >>
  `final_st = cs` by
    (qpat_x_assum `finally _ _ _ = _` mp_tac >>
     qpat_assum `handled body_input = _` mp_tac >>
     qpat_assum `cleanup hs = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `hr` >> Cases_on `cr` >>
     gvs[finally_def, ignore_bind_def, bind_def, return_def, raise_def]) >>
  qpat_x_assum `final_st = cs` SUBST_ALL_TAC >>
  `storage_trace_frame cleanup` by
    (simp[Abbr `cleanup`] >> irule storage_trace_frame_ignore_bind >>
     simp[pop_function_def, storage_trace_frame_state_updates] >>
     Cases_on `release` >>
     simp[storage_trace_frame_return] >> Cases_on `cx.nonreentrant_slot` >>
     simp[storage_trace_frame_return, storage_trace_frame_release_lock]) >>
  `?btail. selected = hs.storage_trace ++ btail` by
    (drule_all storage_trace_frame_prefix >>
     metis_tac[listTheory.APPEND_ASSOC]) >>
  suspend "body_forward"
QED

Resume finite_prefix_Expr_Call_IntCall[body_forward]:
  Cases_on `eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) callable5 body_input` >>
  rename1 `eval_stmts _ _ body_input = (br,bs)` >>
  `hs = bs` by
    (qpat_x_assum `handled body_input = _` mp_tac >>
     simp_tac(srw_ss())[Abbr `handled`, try_def, ignore_bind_def, bind_def] >>
     qpat_assum `eval_stmts _ _ _ = _` (fn th => rewrite_tac[th]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `br`
     >- (simp_tac(srw_ss())[return_def] >> rpt strip_tac >> gvs[]) >>
     simp_tac(srw_ss())[] >>
     disch_then (mp_tac o MATCH_MP vyperEvalPreservesScopesTheory.handle_function_state) >> simp[]) >>
  qpat_x_assum `hs = bs` SUBST_ALL_TAC >>
  `call_evaluation_safe (cx with stk updated_by CONS (src_id_opt,fn))
     (int_calls_stmts callable5)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     simp_tac (srw_ss()) [int_calls_expr_def] >> strip_tac >>
     irule call_evaluation_safe_push_body >> metis_tac[]) >>
  `IS_SOME defaults_st.outcomes` by
    (qpat_assum `finally _ _ args_st = (INL _,defaults_st)` mp_tac >>
     qpat_assum `eval_expr_results _ _ st = (_,args_st)` mp_tac >>
     qpat_assum `IS_SOME st.outcomes` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     drule default_finally_result >> strip_tac >>
     drule (cj 6 vyperEvalOutcomeSuffixTheory.eval_outcome_suffix_mutual) >>
     drule vyperEvalOutcomeSuffixTheory.eval_expr_results_outcome_suffix >>
     gvs[] >> metis_tac[exprOracleStorageInterfacesTheory.outcome_suffix_IS_SOME]) >>
  `IS_SOME lock_st.outcomes` by
    (qpat_x_assum `lock_if_nr _ _ _ _ = _` mp_tac >>
     qpat_x_assum `IS_SOME defaults_st.outcomes` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `callable1` >>
     simp[lock_if_nr_def, return_def] >>
     Cases_on `cx.nonreentrant_slot` >>
     simp[raise_def, ignore_bind_def, bind_def,
       vyperTypeEvalStoragePreservationTheory.acquire_nonreentrant_lock_eq] >>
     rpt IF_CASES_TAC >> simp[check_not_static_eq, return_def] >>
     rpt strip_tac >> gvs[]) >>
  `push_function (src_id_opt,fn) call_env cx lock_st =
     (INL (cx with stk updated_by CONS (src_id_opt,fn)),body_input)` by
    simp[Abbr `body_input`, push_function_def, return_def] >>
  `storage_well_formed_on (cx with stk updated_by CONS (src_id_opt,fn)) body_input (FST H)` by
    metis_tac[Abbr `body_input`, storage_well_formed_on_stk, storage_well_formed_on_scopes] >>
  `valid_horizon (cx with stk updated_by CONS (src_id_opt,fn)) initial_st H body_input.storage_trace` by
    (qpat_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
     qpat_assum `storage_observations_ok cx H lock_st.storage_trace` mp_tac >>
     qpat_assum `Abbrev (body_input = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def, valid_horizon_stk, valid_horizon_def]) >>
  `storage_well_formed_on (cx with stk updated_by CONS (src_id_opt,fn)) bs (FST H) /\
   storage_observations_ok (cx with stk updated_by CONS (src_id_opt,fn)) H bs.storage_trace` by
    (first_x_assum (drule_at (Pat `eval_stmts _ _ _ = _`) o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
     disch_then irule >>
     conj_tac >- simp[Abbr `body_input`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- metis_tac[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`initial_st`,`selected`] >>
     conj_tac
     >- (pure_rewrite_tac [valid_horizon_stk,storage_well_formed_on_stk] >>
         rpt gen_tac >> rpt disch_tac >>
         qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` irule >>
         metis_tac[]) >>
     conj_tac >- metis_tac[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx bs (FST H) /\
   storage_observations_ok cx H bs.storage_trace` by
    metis_tac[storage_well_formed_on_stk, storage_observations_ok_stk] >>
  `storage_trace_backends_well_formed cx (FST H) cs.storage_trace` by
    (qpat_assum `cleanup bs = _` mp_tac >>
     qpat_assum `Abbrev (cleanup = _)` mp_tac >>
     qpat_assum `storage_observations_ok cx H bs.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac(srw_ss())[storage_observations_ok_def, markerTheory.Abbrev_def] >> rpt strip_tac >>
     Cases_on `release` >>
     gvs[pop_function_def, ignore_bind_apply, set_scopes_def, return_def] >>
     Cases_on `cx.nonreentrant_slot` >>
     gvs[return_def, vyperTypeEvalStoragePreservationTheory.release_nonreentrant_lock_eq,
       storage_trace_backends_well_formed_def]) >>
  `storage_observations_ok cx H cs.storage_trace` by
    (qpat_assum `selected = cs.storage_trace ++ sfx` mp_tac >>
     qpat_assum `EVERY _ (storage_trace_regions selected)` mp_tac >>
     qpat_assum `EVERY _ (storage_trace_locks selected)` mp_tac >>
     qpat_assum `storage_roots_fit selected` mp_tac >>
     qpat_assum `storage_trace_backends_well_formed cx _ cs.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> gvs[storage_observations_ok_def]) >>
  conj_tac >- (irule intcall_cleanup_preserves_storage_well_formed_on >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl [`F`,`release`,`args_st.scopes`,`cr`,`bs`] >>
    conj_tac >- (qpat_x_assum `cleanup bs = _` mp_tac >>
      simp[Abbr `cleanup`]) >>
    first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Finalise finite_prefix_Expr_Call_IntCall
