(* Ordinary write branches of the selected-prefix evaluator schema. *)
Theory guardSourceOrdinaryWrites
Ancestors
  guardSourceOrdinarySchema vyperInterpreter vyperState vyperStorageFootprint
  vyperTypeEvalSoundness vyperTypeCallGraph vyperTypeSystem
  vyperEvalOutcomeSuffix vyperTypeExprSoundness list vyperStorageTrace
  vyperTypeCallStackSoundness vyperTypeEvalStoragePreservation
  vyperFiniteStoragePreservation guardMutationTrace
Libs
  guardSourceSchemaLib

Theorem finite_prefix_TupleStores_nil_nil:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "TupleStores_nil_nil")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, return_def, valid_horizon_def]
QED

Theorem finite_prefix_TupleStores_cons_nil:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "TupleStores_cons_nil")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, raise_def, valid_horizon_def]
QED

Theorem finite_prefix_TupleStores_nil_cons:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "TupleStores_nil_cons")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, raise_def, valid_horizon_def]
QED

Theorem finite_prefix_TupleStore_TupleTarget:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "TupleStore_TupleTarget")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  fs[well_typed_atarget_def, int_calls_atarget_def] >>
  qpat_x_assum `ty = TupleT tys` SUBST_ALL_TAC >>
  drule value_runtime_typed_tuple_components >> strip_tac >>
  qpat_x_assum `v = ArrayV (TupleV _)` SUBST_ALL_TAC >>
  qpat_x_assum `!vs. _` (qspec_then `vs` mp_tac) >>
  simp_tac(srw_ss())[] >> strip_tac >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then irule >> metis_tac[]
QED

Theorem finite_prefix_TupleStores_cons_cons:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "TupleStores_cons_cons")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `tys`
  >- (qpat_x_assum `LIST_REL _ (_::_) []` mp_tac >> simp[]) >>
  qpat_x_assum `LIST_REL _ (_::_) (_::_)` mp_tac >>
  simp_tac(srw_ss())[LIST_REL_CONS1] >> strip_tac >>
  qpat_x_assum `LIST_REL _ (_::_) (_::_)` mp_tac >>
  simp_tac(srw_ss())[LIST_REL_CONS1] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_atargets (_::_))` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `assign_tuple_targets cx g v st` >>
  rename1 `assign_tuple_targets cx g v st = (answer,middle)` >>
  reverse (Cases_on `answer`)
  >- (simp_tac(srw_ss())[] >> strip_tac >>
      qpat_x_assum `middle = st'` SUBST_ALL_TAC >>
      qpat_x_assum `!s x t. assign_tuple_targets _ _ _ _ = _ ==> _` kall_tac >>
      qpat_x_assum `!initial_st selected env ty st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then irule >> metis_tac[]) >>
  Cases_on `x` >> simp_tac(srw_ss())[] >> strip_tac >>
  `?xs. st'.storage_trace = middle.storage_trace ++ xs` by
    metis_tac[storage_trace_frame_prefix, cj 10 evaluate_storage_trace_frame] >>
  `?tail. selected = middle.storage_trace ++ tail` by metis_tac[APPEND_ASSOC] >>
  `storage_well_formed_on cx middle (FST H) /\
   storage_observations_ok cx H middle.storage_trace` by
    (qpat_x_assum `!initial_st selected env ty st res st0. _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then irule >> metis_tac[]) >>
  `runtime_consistent env cx middle` by
    (qpat_x_assum `!initial_st selected env ty st res st0. _` kall_tac >>
     fs[runtime_consistent_def] >>
     drule_all (cj 9 eval_scc_type_sound_mutual) >> simp[]) >>
  `IS_SOME middle.outcomes` by
    (drule (cj 9 eval_outcome_suffix_mutual) >>
     disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
     Cases_on `st.outcomes` >> Cases_on `middle.outcomes` >> simp[] >> metis_tac[]) >>
  `valid_horizon cx initial_st H middle.storage_trace` by
    (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
     simp_tac(srw_ss())[valid_horizon_def] >> metis_tac[]) >>
  qpat_x_assum `!s x t. assign_tuple_targets _ _ _ _ = _ ==> _` drule >>
  disch_then (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then irule >> metis_tac[]
QED


Theorem finite_prefix_TupleStore_BaseTarget:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "TupleStore_BaseTarget")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_atarget _ _ _` mp_tac >>
  simp_tac(srw_ss())[well_typed_atarget_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_atarget _)` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  rename1 `eval_target_place cx bt st` >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (answer,middle)` >>
  reverse (Cases_on `answer`)
  >- (simp_tac(srw_ss())[] >> strip_tac >>
      qpat_x_assum `middle = st'` SUBST_ALL_TAC >>
      qpat_x_assum `!initial_st selected env ty st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then irule >> metis_tac[]) >>
  simp_tac(srw_ss())[] >> strip_tac >>
  `st'.storage_trace = middle.storage_trace` by metis_tac[write_place_trace_unchanged] >>
  `storage_well_formed_on cx middle (FST H) /\
   storage_observations_ok cx H middle.storage_trace` by
    (qpat_x_assum `!initial_st selected env ty st res st0. _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then irule >> metis_tac[]) >>
  reverse conj_tac >- metis_tac[] >>
  qpat_x_assum `!initial_st selected env ty st res st0. _` kall_tac >>
  drule_all eval_target_place_success_storage_type >>
  simp_tac(srw_ss())[vyperTypeInvariantsTheory.eval_result_typed_def] >> strip_tac >>
  gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  irule write_place_preserves_storage_well_formed_on >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl [`tv`,`middle.storage_trace`] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`res`,`v`] >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule eval_target_place_observed_region >> simp[]
QED

Theorem finite_prefix_Assign_Tuple:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Assign_Tuple")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `eval_stmt cx (Assign (TupleTarget gs) e) st = (res,st')` >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, atarget_accepts_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (er,s1)` >>
  reverse (Cases_on `er`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!s0 tv t s1 v t1. eval_expr _ _ _ = _ /\ _ ==> _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `read_result cx x s1` >>
  rename1 `read_result cx x s1 = (mr,s2)` >>
  `s2 = s1` by metis_tac[read_result_state] >> BasicProvers.VAR_EQ_TAC >>
  reverse (Cases_on `mr`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!s0 tv t s1 v t1. eval_expr _ _ _ = _ /\ _ ==> _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  simp_tac(srw_ss())[] >> strip_tac >>
  `?xs. st'.storage_trace = s1.storage_trace ++ xs` by
    metis_tac[storage_trace_frame_prefix, cj 9 evaluate_storage_trace_frame] >>
  `?tail. selected = s1.storage_trace ++ tail` by metis_tac[APPEND_ASSOC] >>
  `storage_well_formed_on cx s1 (FST H) /\
   storage_observations_ok cx H s1.storage_trace` by
    (qpat_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then (irule o cj 1) >> metis_tac[]) >>
  qpat_x_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _` kall_tac >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  `value_runtime_typed env (expr_type e) x'` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all vyperTypeEvalSoundnessTheory.read_live_result_success_type >> simp[]) >>
  `IS_SOME s1.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >>
     disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
     Cases_on `st.outcomes` >> Cases_on `s1.outcomes` >> simp[] >> metis_tac[]) >>
  `valid_horizon cx initial_st H s1.storage_trace` by
    (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
     simp_tac(srw_ss())[valid_horizon_def] >> metis_tac[]) >>
  qpat_x_assum `!s0 tv t s1 v t1. eval_expr _ _ _ = _ /\ _ ==> _`
    (drule o SIMP_RULE (srw_ss()) []) >>
  disch_then drule >>
  disch_then (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then irule >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> metis_tac[]
QED

Theorem finite_prefix_Assign_Base:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Assign_Base")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `eval_stmt cx (Assign (BaseTarget bt) e) st = (res,st')` >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  `?tty. well_typed_atarget env (BaseTarget bt) tty /\
         type_widens_to env.type_defs (expr_type e) tty /\
         assignable_type env.type_defs tty` by
    metis_tac[vyperTypeArgFitsTheory.atarget_accepts_well_typed_atarget] >>
  qpat_x_assum `well_typed_atarget env (BaseTarget bt) tty`
    (assume_tac o REWRITE_RULE [well_typed_atarget_def]) >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_atarget_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (rhs_res,rhs_st)` >>
  reverse (Cases_on `rhs_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!s pv t s3 v t2. eval_expr _ _ _ = _ /\ _ ==> _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  rename1 `eval_expr cx e st = (INL pv,rhs_st)` >>
  simp_tac(srw_ss())[] >>
  Cases_on `read_result cx pv rhs_st` >>
  rename1 `read_result cx pv rhs_st = (read_res,read_st)` >>
  `read_st = rhs_st` by metis_tac[read_result_state] >> BasicProvers.VAR_EQ_TAC >>
  reverse (Cases_on `read_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!s pv t s3 v t2. eval_expr _ _ _ = _ /\ _ ==> _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  rename1 `read_result cx pv rhs_st = (INL v,rhs_st)` >>
  qpat_x_assum `!s pv t s3 v t2. eval_expr _ _ _ = _ /\ _ ==> _`
    (drule o SIMP_RULE (srw_ss()) []) >> disch_then drule >> strip_tac >>
  simp_tac(srw_ss())[] >>
  Cases_on `eval_target_place cx bt rhs_st` >>
  rename1 `eval_target_place cx bt rhs_st = (target_res,target_st)` >>
  disch_then (mk_asm "write") >>
  `?xs. st'.storage_trace = target_st.storage_trace ++ xs` by
    (Cases_on `target_res` >> asm "write" mp_tac >>
     simp_tac(srw_ss())[] >> strip_tac >>
     metis_tac[write_place_trace_unchanged, APPEND_NIL]) >>
  `?ys. target_st.storage_trace = rhs_st.storage_trace ++ ys` by
    metis_tac[storage_trace_frame_prefix, cj 8 evaluate_storage_trace_frame] >>
  `?tail. selected = rhs_st.storage_trace ++ tail` by metis_tac[APPEND_ASSOC] >>
  `storage_well_formed_on cx rhs_st (FST H) /\
   storage_observations_ok cx H rhs_st.storage_trace` by
    (qpat_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then (irule o cj 1) >> metis_tac[]) >>
  qpat_x_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _` kall_tac >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  `IS_SOME rhs_st.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >>
     disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
     Cases_on `st.outcomes` >> Cases_on `rhs_st.outcomes` >> simp[] >> metis_tac[]) >>
  `valid_horizon cx initial_st H rhs_st.storage_trace` by
    (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
     simp_tac(srw_ss())[valid_horizon_def] >> metis_tac[]) >>
  `storage_well_formed_on cx target_st (FST H) /\
   storage_observations_ok cx H target_st.storage_trace` by
    (qpat_assum `!initial_st selected env ty st res st0. _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then irule >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     metis_tac[APPEND_ASSOC]) >>
  qpat_x_assum `!initial_st selected env ty st res st0. _` kall_tac >>
  asm_x "write" mp_tac >>
  reverse (Cases_on `target_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >> simp[]) >>
  rename1 `eval_target_place cx bt rhs_st = (INL p,target_st)` >>
  simp_tac(srw_ss())[] >> strip_tac >>
  `st'.storage_trace = target_st.storage_trace` by metis_tac[write_place_trace_unchanged] >>
  reverse conj_tac >- metis_tac[] >>
  `value_runtime_typed env (expr_type e) v` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all vyperTypeEvalSoundnessTheory.read_live_result_success_type >> simp[]) >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  `value_runtime_typed env tty v` by
    (gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
  gvs[vyperTypeInvariantsTheory.eval_result_typed_def,
      vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  irule write_place_preserves_storage_well_formed_on >>
  goal_assum (drule_at Any) >>
  qexistsl [`tv'`,`target_st.storage_trace`,`p`,`res`,`target_st`,`v`] >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule eval_target_place_observed_region >> simp[]
QED

Theorem finite_prefix_AnnAssign:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "AnnAssign")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  `get_tenv cx = env.type_defs` by
    fs[vyperTypeExprSoundnessTheory.runtime_consistent_def,
       vyperTypeInvariantsTheory.env_consistent_def, vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `?tyv. evaluate_type env.type_defs typ = SOME tyv` by
    (drule assignable_type_well_formed >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  qpat_x_assum `!tenv s tyv t. _`
    (qspecl_then [`env.type_defs`, `st`, `tyv`, `st`] mp_tac) >>
  (impl_tac >- simp[lift_option_type_def, return_def]) >> strip_tac >>
  simp_tac(srw_ss())[bind_def, lift_option_type_def, return_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  pure_rewrite_tac[LET_THM] >>
  simp_tac(srw_ss())[bind_def, return_def] >>
  qpat_assum `evaluate_type env.type_defs typ = SOME tyv`
    (fn th => rewrite_tac[th, return_def]) >>
  simp_tac(srw_ss())[bind_def, return_def] >>
  qpat_assum `eval_expr cx e st = _` (fn th => rewrite_tac[th]) >>
  reverse (Cases_on `er`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >> BasicProvers.VAR_EQ_TAC >>
  reverse (Cases_on `rr`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  simp_tac(srw_ss())[] >> strip_tac >>
  `st'.accounts = st1.accounts /\ st'.tStorage = st1.tStorage /\
   st'.storage_trace = st1.storage_trace` by
    (qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
     qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
     Cases_on `st1.scopes` >>
     simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def, type_check_def,
          set_scopes_def, return_def, raise_def, assert_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  `storage_well_formed_on cx st1 (FST H) /\
   storage_observations_ok cx H st1.storage_trace` by
    (qpat_x_assum `!initial_st selected env st res st0. _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then (irule o cj 1) >> metis_tac[]) >>
  metis_tac[storage_well_formed_on_backends]
QED

Theorem finite_prefix_Expr_Pop:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Pop")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `eval_expr cx (Pop elem_ty bt) st = (res,st')` >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    fs[int_calls_expr_def] >>
  conj_tac
  >- (strip_tac >>
      drule vyperTypeAssignContextTheory.well_typed_expr_Pop_dynamic_target >> strip_tac >>
      `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by
        simp[well_typed_target_def] >>
      qpat_x_assum `eval_expr cx (Pop _ bt) st = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
      Cases_on `eval_target_place cx bt st` >>
      rename1 `eval_target_place cx bt st = (target_res,middle)` >>
      reverse (Cases_on `target_res`)
      >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
          qpat_x_assum `!initial_st selected env ty st res st0. _`
            (qspecl_then [`initial_st`, `selected`] mp_tac) >>
          disch_then irule >> metis_tac[]) >>
      simp_tac(srw_ss())[] >> strip_tac >>
      `st'.storage_trace = middle.storage_trace` by
        metis_tac[pop_place_trace_unchanged] >>
      `storage_well_formed_on cx middle (FST H) /\
       storage_observations_ok cx H middle.storage_trace` by
        (qpat_x_assum `!initial_st selected env ty st res st0. _`
           (qspecl_then [`initial_st`, `selected`] mp_tac) >>
         disch_then irule >> metis_tac[]) >>
      reverse conj_tac >- metis_tac[] >>
      drule_all eval_target_place_success_storage_type >> strip_tac >>
      gvs[vyperTypeInvariantsTheory.eval_result_typed_def,
          vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
      irule pop_place_preserves_storage_well_formed_on >>
      conj_tac >- (first_assum ACCEPT_TAC) >>
      qexistsl [`tv'`,`n`,`middle.storage_trace`] >>
      goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac >> gvs[] >>
      drule eval_target_place_observed_region >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[Once well_typed_expr_def]
QED

Theorem finite_prefix_Append:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Append")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  reverse conj_asm2_tac
  >- (rename1 `eval_stmt cx (Append bt e) st = (res,st')` >>
      qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Append bt e))` mp_tac >>
      pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
      drule call_evaluation_safe_append_left >> strip_tac >>
      drule call_evaluation_safe_append_right >> strip_tac >>
      qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
      simp_tac(srw_ss())[Once type_stmt_def] >>
      Cases_on `type_place_target env bt` >- simp[NoAsms] >>
      simp[NoAsms] >> rename1 `type_place_target env bt = SOME vt` >>
      Cases_on `vt` >> simp[NoAsms] >>
      rename1 `type_place_target env bt = SOME (Type ty)` >>
      Cases_on `ty` >> simp[NoAsms] >>
      rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty bd))` >>
      Cases_on `bd` >- simp[NoAsms] >> simp[NoAsms] >>
      rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty (Dynamic n)))` >>
      strip_tac >> qpat_x_assum `env = env'` (SUBST_ALL_TAC o SYM) >>
      `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by
        simp[well_typed_target_def] >>
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
      Cases_on `eval_target_place cx bt st` >>
      rename1 `eval_target_place cx bt st = (target_res,st1)` >>
      reverse (Cases_on `target_res`)
      >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
          qpat_x_assum `!s p t. eval_target_place _ _ _ = _ ==> _` kall_tac >>
          qpat_x_assum `!initial_st selected env ty st res st0. _`
            (qspecl_then [`initial_st`, `selected`] mp_tac) >>
          disch_then (irule o cj 2) >> metis_tac[]) >>
      rename1 `eval_target_place cx bt st = (INL p,st1)` >>
      qpat_x_assum `!s p t. eval_target_place _ _ _ = _ ==> _`
        (drule_then strip_assume_tac) >>
      simp_tac(srw_ss())[] >>
      Cases_on `eval_expr cx e st1` >>
      rename1 `eval_expr cx e st1 = (expr_res,st2)` >>
      disch_then (mk_asm "append") >>
      `?xs. st2.storage_trace = st1.storage_trace ++ xs` by
        metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
      `st'.storage_trace = st2.storage_trace` by
        (Cases_on `expr_res` >> asm "append" mp_tac >> simp_tac(srw_ss())[]
         >- (Cases_on `read_result cx x st2` >>
             rename1 `read_result cx x st2 = (rr,rs)` >>
             `rs = st2` by metis_tac[read_result_state] >>
             Cases_on `rr` >> simp_tac(srw_ss())[] >> strip_tac >>
             metis_tac[append_place_trace_unchanged]) >>
         strip_tac >> gvs[]) >>
      `?tail. selected = st1.storage_trace ++ tail` by metis_tac[APPEND_ASSOC] >>
      `storage_well_formed_on cx st1 (FST H) /\
       storage_observations_ok cx H st1.storage_trace` by
        (qpat_x_assum `!initial_st selected env ty st res st0. _`
           (qspecl_then [`initial_st`, `selected`] mp_tac) >>
         disch_then irule >> metis_tac[]) >>
      `runtime_consistent env cx st1` by
        (qpat_x_assum `!initial_st selected env ty st res st0. _` kall_tac >>
         qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
         fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
         drule_all (cj 1 (SPEC_ALL (cj 8 eval_scc_type_sound_mutual))) >> simp[]) >>
      `IS_SOME st1.outcomes` by
        (drule (cj 8 eval_outcome_suffix_mutual) >>
         disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
         Cases_on `st.outcomes` >> Cases_on `st1.outcomes` >> simp[] >> metis_tac[]) >>
      `valid_horizon cx initial_st H st1.storage_trace` by
        metis_tac[valid_horizon_def] >>
      `storage_well_formed_on cx st2 (FST H) /\
       storage_observations_ok cx H st2.storage_trace` by
        (qpat_x_assum `!initial_st selected env st res st0. _`
           (qspecl_then [`initial_st`, `selected`] mp_tac) >>
         disch_then (irule o cj 1) >> metis_tac[]) >>
      metis_tac[]) >>
  irule (cj 1 eval_storage_well_formed_on_mutual) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem finite_prefix_AugAssign:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "AugAssign")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  reverse conj_asm2_tac >- suspend "observations" >>
  irule (cj 1 eval_storage_well_formed_on_mutual) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Resume finite_prefix_AugAssign[observations]:
  rename1 `eval_stmt cx (AugAssign ty bt bop e) st = (res,st')` >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,target_st)` >>
  reverse (Cases_on `target_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!s p t r v u a tv b. _` kall_tac >>
      qpat_x_assum `!initial_st selected env ty st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 2) >> metis_tac[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `read_place cx x target_st` >>
  rename1 `read_place cx x target_st = (read_res,read_st)` >>
  `read_st = target_st` by metis_tac[read_place_state] >>
  qpat_x_assum `read_st = target_st` SUBST_ALL_TAC >>
  reverse (Cases_on `read_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!s p t r v u a tv b. _` kall_tac >>
      qpat_x_assum `!initial_st selected env ty st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 2) >> metis_tac[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `place_type_value cx x target_st` >>
  rename1 `place_type_value cx x target_st = (type_res,type_st)` >>
  `type_st = target_st` by metis_tac[place_type_value_state] >>
  qpat_x_assum `type_st = target_st` SUBST_ALL_TAC >>
  reverse (Cases_on `type_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!s p t r v u a tv b. _` kall_tac >>
      qpat_x_assum `!initial_st selected env ty st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 2) >> metis_tac[]) >>
  simp_tac(srw_ss())[] >>
  qpat_x_assum `!s p t r v u a tv b. _`
    (drule_at_then (Pat `eval_target_place _ _ _ = _`) mp_tac) >>
  disch_then (drule_at_then (Pat `read_place _ _ _ = _`) mp_tac) >>
  disch_then (drule_at_then (Pat `place_type_value _ _ _ = _`) strip_assume_tac) >>
  Cases_on `eval_expr cx e target_st` >>
  rename1 `eval_expr cx e target_st = (rhs_res,rhs_st)` >>
  disch_then (mk_asm "update") >>
  `st'.storage_trace = rhs_st.storage_trace` by
    (Cases_on `rhs_res` >> asm "update" mp_tac >> simp_tac(srw_ss())[]
     >- (Cases_on `read_result cx x''' rhs_st` >>
         rename1 `read_result cx x''' rhs_st = (rr,rs)` >>
         `rs = rhs_st` by metis_tac[read_result_state] >>
         Cases_on `rr` >> simp_tac(srw_ss())[]
         >- (simp_tac(srw_ss())[LET_THM, lift_sum_def, bind_def] >>
             qmatch_goalsub_abbrev_tac `evaluate_binop bound ptv bop cur right` >>
             Cases_on `evaluate_binop bound ptv bop cur right` >>
             simp_tac(srw_ss())[return_def, raise_def] >> strip_tac >>
             metis_tac[write_place_trace_unchanged]) >>
         strip_tac >> metis_tac[]) >>
     strip_tac >> metis_tac[]) >>
  `?xs. rhs_st.storage_trace = target_st.storage_trace ++ xs` by
    metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
  `?tail. selected = target_st.storage_trace ++ tail` by metis_tac[APPEND_ASSOC] >>
  `storage_well_formed_on cx target_st (FST H) /\
   storage_observations_ok cx H target_st.storage_trace` by
    (qpat_x_assum `!initial_st selected env ty st res st0. _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then irule >> metis_tac[]) >>
  `runtime_consistent env cx target_st` by
    (qpat_x_assum `!initial_st selected env ty st res st0. _` kall_tac >>
     qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
     fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all (cj 1 (SPEC_ALL (cj 8 eval_scc_type_sound_mutual))) >> simp[]) >>
  `IS_SOME target_st.outcomes` by
    (drule (cj 8 eval_outcome_suffix_mutual) >>
     disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
     Cases_on `st.outcomes` >> Cases_on `target_st.outcomes` >> simp[] >> metis_tac[]) >>
  `valid_horizon cx initial_st H target_st.storage_trace` by metis_tac[valid_horizon_def] >>
  `storage_well_formed_on cx rhs_st (FST H) /\
   storage_observations_ok cx H rhs_st.storage_trace` by
    (qpat_x_assum `!initial_st selected env st res st0. _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then (irule o cj 1) >> metis_tac[]) >>
  metis_tac[]
QED
Finalise finite_prefix_AugAssign
