(* Non-IntCall branches of the checked fixed-selected-prefix schema. *)
Theory guardSourceCallConstructors
Ancestors
  guardSourceOrdinarySchema guardSourceInstrumentation vyperInterpreter
  vyperFiniteStoragePreservation vyperStorageTrace vyperStorageFootprint
  vyperState vyperTypeSystem vyperTypeCallGraph vyperEvalMisc
  vyperEvalOutcomeSuffix
Libs
  guardSourceSchemaLib

Theorem recursive_prefix_handoff[local]:
  IS_SOME st.outcomes /\
  (!r mid. f st = (r,mid) ==> outcome_suffix st.outcomes mid.outcomes) /\
  (!r mid. f st = (r,mid) /\
     (?tail. selected = mid.storage_trace ++ tail) ==>
     storage_well_formed_on cx mid (FST H) /\
     storage_observations_ok cx H mid.storage_trace) /\
  f st = (rr,mid) /\
  (?delta. out.storage_trace = mid.storage_trace ++ delta) /\
  (?tail. selected = out.storage_trace ++ tail) ==>
  IS_SOME mid.outcomes /\ storage_well_formed_on cx mid (FST H) /\
  storage_observations_ok cx H mid.storage_trace
Proof
  strip_tac >>
  `outcome_suffix st.outcomes mid.outcomes` by metis_tac[] >>
  drule outcome_suffix_modes >> strip_tac >>
  conj_tac >- (Cases_on `st.outcomes` >> Cases_on `mid.outcomes` >> gvs[]) >>
  first_x_assum irule >>
  reverse conj_tac >- (qexists `rr` >> simp[]) >>
  qexists `delta ++ tail` >> simp[listTheory.APPEND_ASSOC]
QED

Theorem finite_prefix_Expr_Call_RawRevert:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Call_RawRevert")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  (qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, raise_def, return_def] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def, return_def] >>
  rpt IF_CASES_TAC >> simp_tac(srw_ss())[bind_def, raise_def, return_def] >>
  strip_tac >>
  `st' = st1` by
    (qpat_x_assum `!initial_st selected env st res st'. _` kall_tac >>
     gvs[lift_option_type_def, return_def, raise_def,
         vyperMiscTheory.option_CASE_rator, AllCaseEqs()]) >>
  qpat_x_assum `st' = st1` SUBST_ALL_TAC >>
  first_x_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  (disch_then irule >> simp[] >>
   conj_tac >- (qexists `env` >> simp[]) >>
   qexistsl [`initial_st`,`selected`] >>
   simp[listTheory.APPEND_ASSOC, listTheory.APPEND] >>
   qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
   qpat_x_assum `selected = _` SUBST_ALL_TAC >> simp[]))
QED

Theorem finite_prefix_Expr_Call_RawLog:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Call_RawLog")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  (qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, raise_def, return_def, push_log_def] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
  disch_tac >>
  `st'.storage_trace = st1.storage_trace /\ st'.accounts = st1.accounts /\
   st'.tStorage = st1.tStorage` suffices_by
    (strip_tac >>
     `storage_well_formed_on cx st1 (FST H) /\
      storage_observations_ok cx H st1.storage_trace` by
       (first_x_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
        disch_then irule >> simp[] >>
        conj_tac >- (qexists `env` >> simp[]) >>
        qexistsl [`initial_st`,`selected`] >> gvs[] >> metis_tac[]) >>
     gvs[] >> metis_tac[iffRL storage_well_formed_on_backends]) >>
  qpat_x_assum `!initial_st selected env st res st'. _` kall_tac >>
  qpat_x_assum `(case er of _ => _ | _ => _) = _` mp_tac >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def, return_def]
  >- (simp_tac(srw_ss())[lift_option_type_def, bind_def, ignore_bind_def,
        type_check_def, assert_def, raise_def, return_def, push_log_def] >>
      Cases_on `LENGTH x = 2` >> simp_tac(srw_ss())[]
      >- (Cases_on `dest_ArrayV (HD x)` >>
          simp_tac(srw_ss())[bind_def, return_def, raise_def]
          >- (strip_tac >> gvs[]) >>
          Cases_on `dest_BytesV (EL 1 x)` >>
          simp_tac(srw_ss())[bind_def, return_def, raise_def]
          >- (strip_tac >> gvs[]) >>
          simp_tac(srw_ss())[LET_THM, bind_def, ignore_bind_def,
            assert_def, return_def, raise_def, push_log_def] >>
          rpt IF_CASES_TAC >> simp_tac(srw_ss())[bind_def, return_def, raise_def] >>
          strip_tac >> gvs[]) >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[])
QED

Theorem finite_prefix_Expr_Call_Send:
  (!cx initial_st st has_gas vs res out selected.
    IS_SOME st.outcomes /\
    valid_horizon cx initial_st H st.storage_trace /\
    storage_well_formed_on cx st (FST H) /\
    eval_send cx has_gas vs st = (res,out) /\
    (?sfx. selected = out.storage_trace ++ sfx) /\
    (!pre q co sfx.
      selected = pre ++ StorageOutcome q co :: sfx /\
      valid_horizon cx initial_st H pre /\
      storage_well_formed_on cx
        (empty_state with <|accounts := q.cr_accounts;
                           tStorage := q.cr_tStorage|>) (FST H) ==>
      storage_well_formed_on cx
        (empty_state with <|accounts := co.co_accounts;
                           tStorage := co.co_tStorage|>) (FST H)) ==>
    storage_well_formed_on cx out (FST H) /\
    storage_observations_ok cx H out.storage_trace) ==>
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Call_Send")
Proof
  disch_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `LENGTH es = if has_gas then 3 else 2` by
    (qpat_assum `MAP expr_type es = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     Cases_on `has_gas` >> simp[]) >>
  qpat_x_assum `!s'' x t. type_check _ _ _ = _ ==> _` mp_tac >>
  simp_tac(srw_ss())[type_check_def, assert_def, return_def, raise_def] >>
  (impl_tac >- simp[]) >> disch_tac >>
  (qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
   simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
     type_check_def, assert_def, return_def, raise_def] >>
   Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
   Cases_on `er` >> simp_tac(srw_ss())[bind_def, return_def, raise_def]
   >- (qpat_assum `LENGTH es = _` (fn th => simp_tac(srw_ss())[th]) >> strip_tac >>
       `?suffix. st'.storage_trace = st1.storage_trace ++ suffix` by
         (qpat_assum `eval_send _ _ _ _ = _`
            (mp_then Any mp_tac storage_trace_frame_prefix) >>
          simp[storage_trace_frame_send]) >>
       `storage_well_formed_on cx st1 (FST H) /\
        storage_observations_ok cx H st1.storage_trace` by
         (first_x_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
          disch_then irule >> simp[] >>
          conj_tac >- (qexists `env` >> simp[]) >>
          qexistsl [`initial_st`,`selected`] >>
          simp[listTheory.APPEND_ASSOC] >>
          qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
          qpat_x_assum `selected = _` SUBST_ALL_TAC >>
          qpat_x_assum `st'.storage_trace = _` SUBST_ALL_TAC >>
          simp[listTheory.APPEND_ASSOC]) >>
       `IS_SOME st1.outcomes` by
         (qpat_x_assum `!initial_st selected env st res st'. _` kall_tac >>
          qpat_x_assum `!cx initial_st st has_gas vs res out selected. _` kall_tac >>
          mp_tac (cj 6 eval_outcomes_suffix_mutual) >>
          simp_tac(srw_ss())[outcomes_suffix_def] >>
          disch_then (qspecl_then [`cx`,`es`,`st`] mp_tac) >>
          simp[outcome_suffix_def] >> strip_tac >> gvs[]) >>
       qpat_x_assum `!cx initial_st st has_gas vs res out selected. _` irule >>
       goal_assum (drule_at (Pat `eval_send _ _ _ _ = _`)) >>
       qexistsl [`initial_st`,`selected`] >>
       qpat_x_assum `!initial_st selected env st res st'. _` kall_tac >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` kall_tac >>
       simp[] >>
       qpat_x_assum `valid_horizon cx initial_st H _` mp_tac >>
       simp[valid_horizon_def]) >>
   qpat_assum `LENGTH es = _` (fn th => simp_tac(srw_ss())[th]) >>
   strip_tac >> qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
   first_x_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
   disch_then irule >> simp[] >>
   conj_tac >- (qexists `env` >> simp[]) >>
   qexistsl [`initial_st`,`selected`] >> simp[] >>
   qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
   qpat_x_assum `selected = _` SUBST_ALL_TAC >> simp[])
QED

Theorem finite_prefix_Expr_Call_RawCallTarget:
  (!cx initial_st st flags target calldata amount gas res out selected.
    IS_SOME st.outcomes /\
    valid_horizon cx initial_st H st.storage_trace /\
    storage_well_formed_on cx st (FST H) /\
    eval_raw_call cx flags target calldata amount gas st = (res,out) /\
    (?sfx. selected = out.storage_trace ++ sfx) /\
    (!pre q co sfx.
      selected = pre ++ StorageOutcome q co :: sfx /\
      valid_horizon cx initial_st H pre /\
      storage_well_formed_on cx
        (empty_state with <|accounts := q.cr_accounts;
                           tStorage := q.cr_tStorage|>) (FST H) ==>
      storage_well_formed_on cx
        (empty_state with <|accounts := co.co_accounts;
                           tStorage := co.co_tStorage|>) (FST H)) ==>
    storage_well_formed_on cx out (FST H) /\
    storage_observations_ok cx H out.storage_trace) ==>
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Call_RawCallTarget")
Proof
  disch_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  (Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
   `st' = st1 \/ ?target calldata amount gas.
      eval_raw_call cx flags target calldata amount gas st1 = (res,st')` by
     (qpat_x_assum `!initial_st selected env st res st'. _` kall_tac >>
      qpat_x_assum `!cx initial_st st flags target calldata amount gas res out selected. _` kall_tac >>
      qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
        type_check_def, assert_def, raise_def, return_def] >>
      Cases_on `er` >> simp_tac(srw_ss())[bind_def, return_def, raise_def,
        lift_option_type_def] >>
      rpt IF_CASES_TAC >> simp_tac(srw_ss())[bind_def, return_def, raise_def,
        AllCaseEqs()] >> rpt strip_tac >>
      gvs[vyperMiscTheory.option_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
      metis_tac[])
   >- (qpat_x_assum `st' = st1` SUBST_ALL_TAC >>
       first_x_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
       disch_then irule >> simp[] >>
       conj_tac >- (qexists `env` >> simp[]) >>
       qexistsl [`initial_st`,`selected`] >> simp[] >>
       qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
       qpat_x_assum `selected = _` SUBST_ALL_TAC >> simp[]) >>
   `?delta. st'.storage_trace = st1.storage_trace ++ delta` by
     (qpat_assum `eval_raw_call _ _ _ _ _ _ _ = _`
        (mp_then Any mp_tac storage_trace_frame_prefix) >>
      simp[storage_trace_frame_raw_call]) >>
   `IS_SOME st1.outcomes /\ storage_well_formed_on cx st1 (FST H) /\
    storage_observations_ok cx H st1.storage_trace` by
     (irule (INST_TYPE [alpha |-> ``:value list + vyperState$exception``]
        recursive_prefix_handoff) >>
      qexistsl [`eval_exprs cx es`,`st'`,`er`,`selected`,`st`] >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          first_x_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
          disch_then irule >> simp[] >>
          conj_tac >- (qexists `env` >> simp[]) >>
          qexistsl [`initial_st`,`selected`] >> simp[] >>
          qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
          qpat_x_assum `selected = _` SUBST_ALL_TAC >> simp[]) >>
      conj_tac
      >- (mp_tac (cj 6 eval_outcomes_suffix_mutual) >>
          simp_tac(srw_ss())[outcomes_suffix_def] >>
          metis_tac[pairTheory.SND]) >>
      simp[]) >>
   qpat_x_assum `!cx initial_st st flags target calldata amount gas res out selected. _` irule >>
   goal_assum (drule_at (Pat `eval_raw_call _ _ _ _ _ _ _ = _`)) >>
   qexistsl [`initial_st`,`selected`] >>
   qpat_x_assum `!initial_st selected env st res st'. _` kall_tac >>
   conj_tac >- first_assum ACCEPT_TAC >>
   qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` kall_tac >>
   simp[] >>
   qpat_x_assum `valid_horizon cx initial_st H _` mp_tac >>
   simp[valid_horizon_def])
QED
