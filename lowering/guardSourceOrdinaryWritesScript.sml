(* Ordinary write branches of the selected-prefix evaluator schema. *)
Theory guardSourceOrdinaryWrites
Ancestors
  guardSourceOrdinarySchema vyperInterpreter vyperState vyperStorageFootprint
  vyperTypeEvalSoundness vyperTypeCallGraph vyperTypeSystem
  vyperEvalOutcomeSuffix vyperTypeExprSoundness list vyperStorageTrace
  vyperTypeCallStackSoundness
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
