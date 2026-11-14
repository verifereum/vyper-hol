(* Loop branches of the checked selected-prefix schema. *)
Theory guardSourceOrdinaryLoops
Ancestors
  list guardSourceOrdinarySchema vyperInterpreter vyperState vyperStorageFootprint
  vyperTypeSystem vyperTypeCallGraph vyperEvalMisc vyperStorageTrace
  vyperTypeStmtSoundness vyperTypeExprSoundness vyperTypeCallStackSoundness
  vyperEvalOutcomeSuffix vyperTypeEvalStoragePreservation vyperStatePreservation
  vyperFiniteStoragePreservation vyperTypeExtCallCore vyperTypeEvalSoundness
Libs
  guardSourceSchemaLib

Theorem finite_prefix_For:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "For")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_iterator it) /\
   call_evaluation_safe cx (int_calls_stmts body')` by
    (qpat_assum `call_evaluation_safe cx (int_calls_stmt (For id typ it n body'))` mp_tac >>
     pure_rewrite_tac[int_calls_stmt_def] >>
     metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  `env.type_defs = get_tenv cx` by
    metis_tac[runtime_consistent_get_tenv] >>
  `?env_after. type_stmts (extend_local env id typ F) ret_ty body' = SOME env_after` by
    (qpat_x_assum `IS_SOME (type_stmts _ _ _)` mp_tac >>
     rewrite_tac[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_type_def,
    check_def, return_def, raise_def, LET_THM, AllCaseEqs()] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> simp_tac(srw_ss())[]
  >- (qpat_x_assum `!a b c d e f g h i j. _` kall_tac >>
      qpat_x_assum `!a b c d. _` kall_tac >>
      rpt strip_tac >> gvs[bind_def, return_def, raise_def, valid_horizon_def]) >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME iter_tyv` >>
  qpat_x_assum `!a b c d. _`
    (qspecl_then [`get_tenv cx`, `st`, `iter_tyv`, `st`] mp_tac) >>
  (impl_tac >-
    (qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv`
       (fn th => simp_tac(srw_ss())[th, lift_option_type_def, return_def]))) >>
  strip_tac >>
  Cases_on `eval_iterator cx it st` >>
  rename1 `eval_iterator cx it st = (ir,st1)` >>
  qpat_x_assum `case it of Array _ => _ | Range _ _ => _` kall_tac >>
  reverse (Cases_on `ir`) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def] >>
  qpat_assum `eval_iterator cx it st = _` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[]
  >- (strip_tac >> qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
      qpat_x_assum `!a b c d e f g h i j. _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then irule >> metis_tac[]) >>
  rename1 `eval_iterator cx it st = (INL vs,st1)` >>
  Cases_on `compatible_bound (Dynamic n) (LENGTH vs)` >>
  simp_tac(srw_ss())[check_def, assert_def, bind_def, ignore_bind_def,
                      return_def, raise_def] >> asm_rewrite_tac[] >> simp_tac(srw_ss())[]
  >- (strip_tac >> suspend "loop") >>
  strip_tac >> qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
  qpat_x_assum `!a b c d e f g h i j. _` kall_tac >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then irule >> metis_tac[]
QED

Resume finite_prefix_For[loop]:
  `?suffix. st'.storage_trace = st1.storage_trace ++ suffix` by
    (qpat_assum `eval_for cx _ _ _ _ _ = _`
       (mp_then (Pat `f st = _`) mp_tac storage_trace_frame_prefix) >>
     simp[cj 4 evaluate_storage_trace_frame]) >>
  `?tail. selected = st1.storage_trace ++ tail` by metis_tac[APPEND_ASSOC] >>
  `storage_well_formed_on cx st1 (FST H) /\
   storage_observations_ok cx H st1.storage_trace` by
    (qpat_x_assum `!a b c d e f g h i j. _` kall_tac >>
     qpat_x_assum `!initial_st selected env ty st res st0. _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then irule >> metis_tac[]) >>
  `runtime_consistent env cx st1 /\ EVERY (iterator_result_typed iter_tyv) vs` by
    (qpat_x_assum `!a b c d e f g h i j. _` kall_tac >>
     qpat_x_assum `!initial_st selected env ty st res st0. _` kall_tac >>
     fs[runtime_consistent_def] >>
     drule_all (cj 3 eval_scc_type_sound_mutual) >> simp[]) >>
  `IS_SOME st1.outcomes` by
    (qpat_assum `eval_iterator cx it st = _`
       (mp_then Any mp_tac (cj 3 eval_outcome_suffix_mutual)) >>
     disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
     Cases_on `st.outcomes` >> Cases_on `st1.outcomes` >> simp[] >> metis_tac[]) >>
  `valid_horizon cx initial_st H st1.storage_trace` by
    (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
     simp_tac(srw_ss())[valid_horizon_def] >> metis_tac[]) >>
  qpat_x_assum `!a b c d e f g h i j. _`
    (qspecl_then [`get_tenv cx`, `st`, `iter_tyv`, `st`, `st`, `vs`, `st1`, `st1`, `()`, `st1`] mp_tac) >>
  (impl_tac >-
    (qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv`
       (fn th => simp_tac(srw_ss())[th, lift_option_type_def, return_def]) >>
     simp[check_def, assert_def, return_def])) >>
  disch_then (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then irule >> metis_tac[]
QED
Finalise finite_prefix_For

Theorem finite_prefix_For_cons:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "For_cons")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    push_scope_with_var_def, return_def] >>
  Cases_on `read_result cx r st` >>
  rename1 `read_result cx r st = (read_res,read_st)` >>
  drule read_result_state >> strip_tac >>
  qpat_x_assum `read_st = st` SUBST_ALL_TAC >>
  reverse (Cases_on `read_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >>
      qpat_x_assum `!a b c d e f g h i. _` kall_tac >>
      qpat_x_assum `!a b c d e f. _` kall_tac >>
      gvs[valid_horizon_def]) >>
  rename1 `read_result cx r st = (INL v,st)` >>
  `value_has_type tyv v` by
    (qpat_assum `EVERY _ (_::_)` (strip_assume_tac o REWRITE_RULE [EVERY_DEF]) >>
     drule_all iterator_result_read_typed >> simp[]) >>
  simp_tac(srw_ss())[] >>
  qmatch_goalsub_abbrev_tac `finally loop_body pop_scope stp` >>
  `push_scope_with_var nm tyv v st = (INL (),stp)` by
    simp[push_scope_with_var_def, return_def, Abbr `stp`] >>
  qpat_x_assum `!a b c d e f. _`
    (qspecl_then [`st`, `v`, `st`, `st`, `()`, `stp`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  Cases_on `finally loop_body pop_scope stp` >>
  rename1 `finally loop_body pop_scope stp = (lr,st_after)` >> strip_tac >>
  qunabbrev_tac `loop_body` >>
  drule_all (SRULE [ignore_bind_def] pushed_loop_cleanup) >> strip_tac >>
  `runtime_consistent (extend_local env nm ty F) cx stp` by
    (drule_all push_loop_runtime_consistent >> simp[]) >>
  `storage_well_formed_on cx stp (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >> qexists `st` >>
     simp[Abbr `stp`]) >>
  `?tail. selected = st_after.storage_trace ++ tail` by
    (qpat_x_assum `!a b c d e f g h i. _` kall_tac >>
     qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. _` kall_tac >>
     Cases_on `lr` >> fs[return_def, AllCaseEqs()]
     >- (Cases_on `x` >> fs[return_def]
         >- gvs[] >>
         (`?suffix. st'.storage_trace = st_after.storage_trace ++ suffix` by
               (qpat_assum `eval_for _ _ _ _ rs _ = _`
                 (mp_then (Pat `f st = _`) mp_tac storage_trace_frame_prefix) >>
                simp[cj 4 evaluate_storage_trace_frame]) >>
             qexists `suffix ++ sfx` >> simp[APPEND_ASSOC]) >>
         gvs[]) >>
     gvs[]) >>
  `?tail. selected = st_body.storage_trace ++ tail` by
    (qexists `tail` >>
     qpat_x_assum `selected = st_after.storage_trace ++ tail` mp_tac >>
     qpat_assum `st_after = _` (fn th => simp_tac(srw_ss())[th])) >>
  `IS_SOME stp.outcomes /\ valid_horizon cx initial_st H stp.storage_trace` by
    simp[Abbr `stp`] >>
  `storage_well_formed_on cx st_body (FST H) /\
   storage_observations_ok cx H st_body.storage_trace` by
    (qpat_x_assum `!a b c d e f g h i. _` kall_tac >>
     qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then irule >> metis_tac[]) >>
  qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. _` kall_tac >>
  `storage_well_formed_on cx st_after (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >> qexists `st_body` >>
     qpat_assum `st_after = _` (fn th => simp[th])) >>
  `storage_observations_ok cx H st_after.storage_trace` by
    (qpat_x_assum `!a b c d e f g h i. _` kall_tac >>
     qpat_assum `st_after = _` (fn th => simp[th])) >>
  Cases_on `lr` >> fs[return_def, AllCaseEqs()]
  >- (Cases_on `x` >> fs[return_def]
      >- metis_tac[] >>
      suspend "continue") >>
  metis_tac[]
QED

Resume finite_prefix_For_cons[continue]:
  `runtime_consistent env cx st_after` by
    (qpat_x_assum `!a b c d e f g. _` kall_tac >>
     fs[runtime_consistent_def] >>
     qpat_assum `eval_for _ _ _ _ [_] _ = _`
       (mp_then Any mp_tac (cj 4 eval_scc_type_sound_mutual)) >>
     disch_then (drule_all o SRULE [iterator_result_typed_def]) >> simp[] >> fs[]) >>
  `IS_SOME st_after.outcomes` by
    (qpat_assum `eval_stmts cx body' stp = _`
       (mp_then Any mp_tac (cj 2 eval_outcome_suffix_mutual)) >>
     disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
     qpat_x_assum `!a b c d e f g. _` kall_tac >>
     Cases_on `stp.outcomes` >> Cases_on `st_body.outcomes` >>
     simp[] >> qpat_assum `st_after = _` (fn th => simp[th]) >> metis_tac[]) >>
  `valid_horizon cx initial_st H st_after.storage_trace` by
    (qpat_x_assum `!a b c d e f g. _` kall_tac >>
     qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
     simp_tac(srw_ss())[valid_horizon_def] >> metis_tac[]) >>
  qpat_x_assum `!a b c d e f g. _`
    (qspecl_then [`st`, `v`, `st`, `st`, `stp`, `stp`,
                  `st_body with scopes := TL st_body.scopes`] mp_tac) >>
  (impl_tac >- simp[ignore_bind_def]) >> strip_tac >>
  first_x_assum (qspecl_then [`initial_st`, `st_body.storage_trace ++ tail`] mp_tac) >>
  disch_then irule >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`env`, `env_after`, `res`, `ret_ty`, `st_after`, `ty`] >>
  simp[]
QED
Finalise finite_prefix_For_cons
