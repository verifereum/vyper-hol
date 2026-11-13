(* Non-IntCall branches of the checked fixed-selected-prefix schema. *)
Theory guardSourceCallConstructors
Ancestors
  guardSourceOrdinarySchema guardSourceInstrumentation vyperInterpreter
  vyperFiniteStoragePreservation vyperStorageTrace vyperStorageFootprint
  vyperState vyperTypeSystem vyperTypeCallGraph vyperEvalMisc
  vyperEvalOutcomeSuffix vyperTypeEvalSoundness vyperTypeCallStackSoundness
  vyperTypeEvalStoragePreservation
Libs
  guardSourceSchemaLib

fun prefix_assumption_tac (asl,w) =
  if is_exists w then (qexists `tail` >> first_assum ACCEPT_TAC) (asl,w)
  else first_assum
    (ACCEPT_TAC o PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND])
    (asl,w);

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

Theorem finite_prefix_Expr_Call_RawCallCalldataTarget:
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
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Call_RawCallCalldataTarget")
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

Theorem finite_prefix_Expr_Call_SelfDestructTarget:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Call_SelfDestructTarget")
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
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
  `st'.storage_trace = st1.storage_trace /\
   (!b. get_storage cx st' b = get_storage cx st1 b)` suffices_by
    (strip_tac >>
     `storage_well_formed_on cx st1 (FST H) /\
      storage_observations_ok cx H st1.storage_trace` by
       (first_x_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
        disch_then irule >> simp[] >>
        conj_tac >- (qexists `env` >> simp[]) >>
        qexistsl [`initial_st`,`selected`] >> simp[] >>
        qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
        qpat_x_assum `selected = _` SUBST_ALL_TAC >> simp[]) >>
     fs[storage_well_formed_on_def]) >>
  qpat_x_assum `!initial_st selected env st res st'. _` kall_tac >>
  qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, raise_def, return_def] >>
  qpat_assum `eval_exprs cx es st = _` (fn th => pure_rewrite_tac[th]) >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def, return_def] >>
  simp_tac(srw_ss())[lift_option_type_def, bind_def, ignore_bind_def,
    get_accounts_def, return_def, raise_def, LET_THM] >>
  Cases_on `LENGTH x = 1` >> simp_tac(srw_ss())[]
  >- (Cases_on `dest_AddressV (HD x)` >>
      simp_tac(srw_ss())[bind_def, return_def, raise_def]
      >- (strip_tac >> gvs[]) >>
      Cases_on `cx.txn.is_static` >> simp_tac(srw_ss())[]
      >- (strip_tac >> gvs[]) >>
      qpat_x_assum `!pre rq co sfx. _` kall_tac >>
      simp[transfer_value_def, bind_def, ignore_bind_def,
        get_accounts_def, LET_THM, assert_def, check_def, return_def, raise_def,
        update_accounts_def, update_pending_deletions_def] >>
      rpt IF_CASES_TAC >>
      simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
        get_accounts_def, check_def, assert_def,
        update_accounts_def, update_pending_deletions_def] >>
      rpt IF_CASES_TAC >> simp_tac(srw_ss())[bind_def, ignore_bind_def,
        return_def, raise_def, update_accounts_def, update_pending_deletions_def] >>
      strip_tac >> gvs[] >>
      gen_tac >> Cases_on `b` >>
      simp[vyperStorageBackendTheory.get_storage_def,
        vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
        combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >>
      rpt IF_CASES_TAC >> gvs[combinTheory.APPLY_UPDATE_THM]) >>
  strip_tac >> gvs[]
QED

Theorem finite_prefix_Expr_Call_ExtCall:
  (!cx initial_st st is_static skip_check sig opts vs res out selected.
    IS_SOME st.outcomes /\
    valid_horizon cx initial_st H st.storage_trace /\
    storage_well_formed_on cx st (FST H) /\
    eval_ext_call cx is_static skip_check sig opts vs st = (res,out) /\
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
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Call_ExtCall")
Proof
  disch_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
     irule call_evaluation_safe_append_left >> goal_assum (drule_at Any)) >>
  `well_typed_exprs env es` by metis_tac[vyperTypeBuiltinsTheory.ext_call_args_typed] >>
  PairCases_on `sig` >>
  `well_typed_exprs env (TAKE 1 es) /\
   well_typed_exprs env (TAKE (LENGTH sig1) (DROP 1 es)) /\
   well_typed_exprs env (DROP (1 + LENGTH sig1) es)` by
    metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE 1 es)) /\
   call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH sig1) (DROP 1 es))) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (1 + LENGTH sig1) es))` by
    metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  pure_rewrite_tac[Once evaluate_def] >> simp_tac(srw_ss())[LET_THM] >>
  qmatch_goalsub_abbrev_tac `bind (eval_exprs cx (TAKE 1 es)) cont` >>
  `!v. storage_trace_frame (cont v)` by
    (simp[Abbr `cont`] >> gen_tac >>
     irule storage_trace_frame_bind_all >>
     simp[cj 11 evaluate_storage_trace_frame] >> gen_tac >>
     irule storage_trace_frame_bind_all >>
     simp[cj 6 evaluate_storage_trace_frame] >> gen_tac >>
     irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_results, storage_trace_frame_ext_call]) >>
  Cases_on `eval_exprs cx (TAKE 1 es) st` >>
  rename1 `eval_exprs cx (TAKE 1 es) st = (target_res,target_st)` >>
  qpat_assum `eval_exprs cx (TAKE 1 es) st = _`
    (fn th => pure_rewrite_tac[bind_def, th]) >>
  Cases_on `target_res` >> simp_tac(srw_ss())[raise_def]
  >- (rename1 `eval_exprs cx (TAKE 1 es) st = (INL target,target_st)` >>
      disch_tac >>
      `?delta. st'.storage_trace = target_st.storage_trace ++ delta` by
        (irule (INST_TYPE [alpha |-> ``:eval_result``] storage_trace_frame_prefix) >>
         goal_assum (drule_at Any) >> simp[]) >>
      `IS_SOME target_st.outcomes /\
       storage_well_formed_on cx target_st (FST H) /\
       storage_observations_ok cx H target_st.storage_trace` by
        (qpat_x_assum `!s'' target t nargs. eval_exprs _ _ _ = _ /\ _ ==> _` kall_tac >>
         qpat_x_assum `!s'' target t nargs s1 rs t1. eval_exprs _ _ _ = _ /\ _ ==> _` kall_tac >>
         irule (INST_TYPE [alpha |-> ``:value list + vyperState$exception``]
           recursive_prefix_handoff) >>
         qexistsl [`eval_exprs cx (TAKE 1 es)`,`st'`,`INL target`,`selected`,`st`] >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             qpat_x_assum `!initial_st selected env st res st'. _`
               (qspecl_then [`initial_st`,`selected`,`env`,`st`,`r`,`mid`] mp_tac) >>
             disch_then irule >> rpt conj_tac >>
             prefix_assumption_tac) >>
         conj_tac
         >- (mp_tac (cj 6 eval_outcomes_suffix_mutual) >>
             simp_tac(srw_ss())[outcomes_suffix_def] >>
             metis_tac[pairTheory.SND]) >>
         simp[]) >>
      `runtime_consistent env cx target_st` by
        (drule_all eval_exprs_preserves_runtime_consistent >>
         disch_then ACCEPT_TAC) >>
      `valid_horizon cx initial_st H target_st.storage_trace` by
        (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
         pure_rewrite_tac[valid_horizon_def] >> strip_tac >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `!s'' target t nargs. eval_exprs _ _ _ = _ /\ _ ==> _`
        (drule o SIMP_RULE (srw_ss()) []) >> strip_tac >>
      qpat_x_assum `!v. storage_trace_frame (cont v)` kall_tac >>
      qpat_x_assum `cont target target_st = _` mp_tac >>
      simp_tac(srw_ss())[Abbr `cont`] >>
      qmatch_goalsub_abbrev_tac `bind (eval_expr_results cx (TAKE (LENGTH sig1) (DROP 1 es))) capture_cont` >>
      `!v. storage_trace_frame (capture_cont v)` by
        (simp[Abbr `capture_cont`] >> gen_tac >>
         irule storage_trace_frame_bind_all >>
         simp[cj 6 evaluate_storage_trace_frame] >> gen_tac >>
         irule storage_trace_frame_bind_all >>
         simp[storage_trace_frame_read_results, storage_trace_frame_ext_call]) >>
      Cases_on `eval_expr_results cx (TAKE (LENGTH sig1) (DROP 1 es)) target_st` >>
      rename1 `eval_expr_results _ _ target_st = (capture_res,capture_st)` >>
      disch_tac >>
      `?delta. st'.storage_trace = capture_st.storage_trace ++ delta` by
        (qpat_x_assum `bind _ capture_cont target_st = _` mp_tac >>
         qpat_assum `eval_expr_results _ _ target_st = _`
           (fn th => pure_rewrite_tac[bind_def, th]) >>
         Cases_on `capture_res` >> simp_tac(srw_ss())[raise_def] >> strip_tac
         >- (irule (INST_TYPE [alpha |-> ``:eval_result``] storage_trace_frame_prefix) >>
             goal_assum (drule_at Any) >> simp[]) >>
         gvs[]) >>
      `IS_SOME capture_st.outcomes /\
       storage_well_formed_on cx capture_st (FST H) /\
       storage_observations_ok cx H capture_st.storage_trace` by
        (qpat_x_assum `!s'' target t nargs s1 rs t1. eval_exprs _ _ _ = _ /\ _ ==> _` kall_tac >>
         qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (TAKE 1 es) /\ _ ==> _` kall_tac >>
         irule (INST_TYPE [alpha |-> ``:eval_result list + vyperState$exception``]
           recursive_prefix_handoff) >>
         qexistsl [`eval_expr_results cx (TAKE (LENGTH sig1) (DROP 1 es))`,
                   `st'`,`capture_res`,`selected`,`target_st`] >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             qpat_x_assum `!initial_st selected env st res st'. _`
               (qspecl_then [`initial_st`,`selected`,`env`,`target_st`,`r`,`mid`] mp_tac) >>
             disch_then irule >>
             pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
             rpt conj_tac >>
             prefix_assumption_tac) >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             drule eval_expr_results_outcome_suffix >> disch_then ACCEPT_TAC) >>
         simp[]) >>
      `valid_horizon cx initial_st H capture_st.storage_trace` by
        (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
         pure_rewrite_tac[valid_horizon_def] >> strip_tac >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `runtime_consistent env cx capture_st` by
        (drule_all eval_expr_results_preserves_runtime_consistent_from_eval >>
         disch_then ACCEPT_TAC) >>
      qpat_x_assum `bind _ capture_cont target_st = _` mp_tac >>
      qpat_assum `eval_expr_results _ _ target_st = _`
        (fn th => pure_rewrite_tac[bind_def, th]) >>
      reverse (Cases_on `capture_res`) >> simp_tac(srw_ss())[raise_def]
      >- (strip_tac >> qpat_x_assum `capture_st = st'` SUBST_ALL_TAC >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      rename1 `eval_expr_results _ _ target_st = (INL results,capture_st)` >>
      qpat_x_assum `!s'' target t nargs s1 rs t1. eval_exprs _ _ _ = _ /\ _ ==> _`
        (drule o SIMP_RULE (srw_ss()) []) >>
      disch_then drule >> strip_tac >>
      qpat_x_assum `!v. storage_trace_frame (capture_cont v)` kall_tac >>
      simp_tac(srw_ss())[Abbr `capture_cont`] >>
      qmatch_goalsub_abbrev_tac `bind (eval_exprs cx (DROP (1 + LENGTH sig1) es)) kwargs_cont` >>
      `!v. storage_trace_frame (kwargs_cont v)` by
        (simp[Abbr `kwargs_cont`] >> gen_tac >>
         irule storage_trace_frame_bind_all >>
         simp[storage_trace_frame_read_results, storage_trace_frame_ext_call]) >>
      Cases_on `eval_exprs cx (DROP (1 + LENGTH sig1) es) capture_st` >>
      rename1 `eval_exprs _ _ capture_st = (kwargs_res,kwargs_st)` >>
      disch_tac >>
      `?delta. st'.storage_trace = kwargs_st.storage_trace ++ delta` by
        (qpat_x_assum `bind _ kwargs_cont capture_st = _` mp_tac >>
         qpat_assum `eval_exprs _ _ capture_st = _`
           (fn th => pure_rewrite_tac[bind_def, th]) >>
         Cases_on `kwargs_res` >> simp_tac(srw_ss())[raise_def] >> strip_tac
         >- (irule (INST_TYPE [alpha |-> ``:eval_result``] storage_trace_frame_prefix) >>
             goal_assum (drule_at Any) >> simp[]) >>
         gvs[]) >>
      `IS_SOME kwargs_st.outcomes /\
       storage_well_formed_on cx kwargs_st (FST H) /\
       storage_observations_ok cx H kwargs_st.storage_trace` by
        (qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (TAKE 1 es) /\ _ ==> _` kall_tac >>
         qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (TAKE (LENGTH sig1) (DROP 1 es)) /\ _ ==> _` kall_tac >>
         irule (INST_TYPE [alpha |-> ``:value list + vyperState$exception``]
           recursive_prefix_handoff) >>
         qexistsl [`eval_exprs cx (DROP (1 + LENGTH sig1) es)`,
                   `st'`,`kwargs_res`,`selected`,`capture_st`] >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             qpat_x_assum `!initial_st selected env st res st'. _`
               (qspecl_then [`initial_st`,`selected`,`env`,`capture_st`,`r`,`mid`] mp_tac) >>
             disch_then irule >>
             pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
             rpt conj_tac >>
             prefix_assumption_tac) >>
         conj_tac
         >- (mp_tac (cj 6 eval_outcomes_suffix_mutual) >>
             simp_tac(srw_ss())[outcomes_suffix_def] >>
             metis_tac[pairTheory.SND]) >>
         simp[]) >>
      `valid_horizon cx initial_st H kwargs_st.storage_trace` by
        (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
         pure_rewrite_tac[valid_horizon_def] >> strip_tac >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `bind _ kwargs_cont capture_st = _` mp_tac >>
      qpat_assum `eval_exprs _ _ capture_st = _`
        (fn th => pure_rewrite_tac[bind_def, th]) >>
      reverse (Cases_on `kwargs_res`) >> simp_tac(srw_ss())[raise_def]
      >- (strip_tac >> qpat_x_assum `kwargs_st = st'` SUBST_ALL_TAC >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `!v. storage_trace_frame (kwargs_cont v)` kall_tac >>
      simp_tac(srw_ss())[Abbr `kwargs_cont`, bind_apply] >>
      Cases_on `read_results cx results kwargs_st` >>
      rename1 `read_results cx results kwargs_st = (read_res,read_st)` >>
      drule read_results_state >> disch_then SUBST_ALL_TAC >>
      reverse (Cases_on `read_res`) >> simp_tac(srw_ss())[]
      >- (strip_tac >> qpat_x_assum `kwargs_st = st'` SUBST_ALL_TAC >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >>
      qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (TAKE 1 es) /\ _ ==> _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (TAKE (LENGTH sig1) (DROP 1 es)) /\ _ ==> _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (DROP (1 + LENGTH sig1) es) /\ _ ==> _` kall_tac >>
      qpat_x_assum `!cx initial_st st is_static skip_check sig opts vs res out selected. _` irule >>
      goal_assum (drule_at (Pat `eval_ext_call _ _ _ _ _ _ _ = _`)) >>
      qexistsl [`initial_st`,`selected`] >> simp[] >>
      qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
      qpat_x_assum `selected = _` SUBST_ALL_TAC >> simp[]) >>
  strip_tac >> qpat_x_assum `target_st = st'` SUBST_ALL_TAC >>
  qpat_x_assum `!s'' target t nargs. eval_exprs _ _ _ = _ /\ _ ==> _` kall_tac >>
  qpat_x_assum `!s'' target t nargs s1 rs t1. eval_exprs _ _ _ = _ /\ _ ==> _` kall_tac >>
  qpat_x_assum `!v. storage_trace_frame (cont v)` kall_tac >>
  qpat_x_assum `Abbrev _` kall_tac >>
  first_x_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then irule >> simp[] >>
  conj_tac >- (qexists `env` >> simp[]) >>
  qexistsl [`initial_st`,`selected`] >> simp[] >>
  qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
  qpat_x_assum `selected = _` SUBST_ALL_TAC >> simp[]
QED

Theorem finite_prefix_Expr_Call_CreateTarget:
  (!cx initial_st st kind has_salt rof arg_tys vs blueprint_size res out selected.
    IS_SOME st.outcomes /\
    valid_horizon cx initial_st H st.storage_trace /\
    storage_well_formed_on cx st (FST H) /\
    eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (res,out) /\
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
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Call_CreateTarget")
Proof
  disch_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
     irule call_evaluation_safe_append_left >> goal_assum (drule_at Any)) >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  pure_rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  Cases_on `kind` >>
  rule_assum_tac (REWRITE_RULE [vyperASTTheory.create_kind_11, vyperASTTheory.create_kind_distinct]) >>
  ALL_TAC
  >~ [`RawCreate`] >- suspend "PrefixRawCreate"
  >~ [`CreateFromBlueprint raw_args`] >- suspend "PrefixBlueprint" >>
  rule_assum_tac (SIMP_RULE bool_ss
    [vyperASTTheory.create_kind_11, vyperASTTheory.create_kind_distinct]) >>
  (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  reverse (Cases_on `args_res`) >> simp_tac(srw_ss())[]
  >- (strip_tac >> qpat_x_assum `args_st = st'` SUBST_ALL_TAC >>
      first_x_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
      disch_then irule >> simp[] >>
      conj_tac >- (qexists `env` >> simp[]) >>
      qexistsl [`initial_st`,`selected`] >> simp[] >>
      qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
      qpat_x_assum `selected = _` SUBST_ALL_TAC >> simp[]) >>
  rename1 `eval_exprs cx es st = (INL args,args_st)` >> strip_tac >>
  `?delta. st'.storage_trace = args_st.storage_trace ++ delta` by
    (qpat_assum `eval_create _ _ _ _ _ _ _ _ = _`
       (mp_then Any mp_tac storage_trace_frame_prefix) >>
     simp[storage_trace_frame_create]) >>
  `IS_SOME args_st.outcomes /\
   storage_well_formed_on cx args_st (FST H) /\
   storage_observations_ok cx H args_st.storage_trace` by
    (irule (INST_TYPE [alpha |-> ``:value list + vyperState$exception``]
       recursive_prefix_handoff) >>
     qexistsl [`eval_exprs cx es`,`st'`,`INL args`,`selected`,`st`] >>
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
  qpat_x_assum `!cx initial_st st kind has_salt rof arg_tys vs blueprint_size res out selected. _` irule >>
  goal_assum (drule_at (Pat `eval_create _ _ _ _ _ _ _ _ = _`)) >>
  qexistsl [`initial_st`,`selected`] >>
  qpat_x_assum `!initial_st selected env st res st'. _` kall_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` kall_tac >>
  simp[] >>
  qpat_x_assum `valid_horizon cx initial_st H _` mp_tac >>
  simp[valid_horizon_def])
QED

Resume finite_prefix_Expr_Call_CreateTarget[PrefixRawCreate]:
  markerLib.RESUME_TAC >>
  rule_assum_tac (SIMP_RULE bool_ss
    [vyperASTTheory.create_kind_11, vyperASTTheory.create_kind_distinct]) >>
  `well_typed_exprs env (TAKE 2 es) /\
   well_typed_exprs env (TAKE (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)) /\
   well_typed_exprs env (DROP (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es))` by
    metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE 2 es)) /\
   call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es))) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)))` by
    metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  pure_rewrite_tac[Once evaluate_def] >>
  simp_tac(srw_ss())[LET_THM, listTheory.LENGTH_DROP] >>
  qmatch_goalsub_abbrev_tac `bind (eval_exprs cx (TAKE 2 es)) prefix_cont` >>
  `!v. storage_trace_frame (prefix_cont v)` by
    (simp[Abbr `prefix_cont`] >> gen_tac >>
     irule storage_trace_frame_bind_all >>
     simp[cj 11 evaluate_storage_trace_frame] >> gen_tac >>
     irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_results] >> gen_tac >>
     irule storage_trace_frame_bind_all >>
     simp[cj 6 evaluate_storage_trace_frame, storage_trace_frame_create]) >>
  Cases_on `eval_exprs cx (TAKE 2 es) st` >>
  rename1 `eval_exprs cx (TAKE 2 es) st = (prefix_res,prefix_st)` >>
  qpat_assum `eval_exprs cx (TAKE 2 es) st = _`
    (fn th => pure_rewrite_tac[bind_def, th]) >>
  Cases_on `prefix_res` >> simp_tac(srw_ss())[raise_def]
  >- (rename1 `eval_exprs cx (TAKE 2 es) st = (INL prefix,prefix_st)` >>
      disch_tac >>
      `?delta. st'.storage_trace = prefix_st.storage_trace ++ delta` by
        (irule (INST_TYPE [alpha |-> ``:eval_result``] storage_trace_frame_prefix) >>
         goal_assum (drule_at Any) >> simp[]) >>
      `IS_SOME prefix_st.outcomes /\
       storage_well_formed_on cx prefix_st (FST H) /\
       storage_observations_ok cx H prefix_st.storage_trace` by
        (qpat_x_assum `!s prefix t. eval_exprs _ _ _ = _ ==> _` kall_tac >>
         qpat_x_assum `!s prefix t s1 results t1 s2 args t2. eval_exprs _ _ _ = _ /\ _ ==> _` kall_tac >>
         irule (INST_TYPE [alpha |-> ``:value list + vyperState$exception``]
           recursive_prefix_handoff) >>
         qexistsl [`eval_exprs cx (TAKE 2 es)`,`st'`,`INL prefix`,`selected`,`st`] >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             qpat_x_assum `!initial_st selected env st res st'. _`
               (qspecl_then [`initial_st`,`selected`,`env`,`st`,`r`,`mid`] mp_tac) >>
             disch_then irule >> rpt conj_tac >>
             prefix_assumption_tac) >>
         conj_tac
         >- (mp_tac (cj 6 eval_outcomes_suffix_mutual) >>
             simp_tac(srw_ss())[outcomes_suffix_def] >>
             metis_tac[pairTheory.SND]) >>
         simp[]) >>
      `runtime_consistent env cx prefix_st` by
        (drule_all eval_exprs_preserves_runtime_consistent >> disch_then ACCEPT_TAC) >>
      `valid_horizon cx initial_st H prefix_st.storage_trace` by
        (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
         pure_rewrite_tac[valid_horizon_def] >> strip_tac >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `!s prefix t. eval_exprs _ _ _ = _ ==> _`
        (drule o SIMP_RULE (srw_ss()) []) >> strip_tac >>
      qpat_x_assum `!v. storage_trace_frame (prefix_cont v)` kall_tac >>
      qpat_x_assum `prefix_cont prefix prefix_st = _` mp_tac >>
      simp_tac(srw_ss())[Abbr `prefix_cont`] >>
      qmatch_goalsub_abbrev_tac
        `bind (eval_expr_results cx (TAKE (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es))) capture_cont` >>
      `!v. storage_trace_frame (capture_cont v)` by
        (simp[Abbr `capture_cont`] >> gen_tac >>
         irule storage_trace_frame_bind_all >>
         simp[storage_trace_frame_read_results] >> gen_tac >>
         irule storage_trace_frame_bind_all >>
         simp[cj 6 evaluate_storage_trace_frame, storage_trace_frame_create]) >>
      Cases_on `eval_expr_results cx (TAKE (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)) prefix_st` >>
      rename1 `eval_expr_results _ _ prefix_st = (capture_res,capture_st)` >>
      disch_tac >>
      `?delta. st'.storage_trace = capture_st.storage_trace ++ delta` by
        (qpat_x_assum `bind _ capture_cont prefix_st = _` mp_tac >>
         qpat_assum `eval_expr_results _ _ prefix_st = _`
           (fn th => pure_rewrite_tac[bind_def, th]) >>
         Cases_on `capture_res` >> simp_tac(srw_ss())[raise_def] >> strip_tac
         >- (irule (INST_TYPE [alpha |-> ``:eval_result``] storage_trace_frame_prefix) >>
             goal_assum (drule_at Any) >> simp[]) >>
         qpat_x_assum `capture_st = st'` SUBST_ALL_TAC >>
         qexists `[]` >> simp_tac(srw_ss())[]) >>
      `IS_SOME capture_st.outcomes /\
       storage_well_formed_on cx capture_st (FST H) /\
       storage_observations_ok cx H capture_st.storage_trace` by
        (qpat_x_assum `!s prefix t s1 results t1 s2 args t2. eval_exprs _ _ _ = _ /\ _ ==> _` kall_tac >>
         qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (TAKE 2 es) /\ _ ==> _` kall_tac >>
         irule (INST_TYPE [alpha |-> ``:eval_result list + vyperState$exception``]
           recursive_prefix_handoff) >>
         qexistsl [`eval_expr_results cx (TAKE (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es))`,
                   `st'`,`capture_res`,`selected`,`prefix_st`] >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             qpat_x_assum `!initial_st selected env st res st'. _`
               (qspecl_then [`initial_st`,`selected`,`env`,`prefix_st`,`r`,`mid`] mp_tac) >>
             disch_then irule >>
             pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
             rpt conj_tac >>
             prefix_assumption_tac) >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             drule eval_expr_results_outcome_suffix >> disch_then ACCEPT_TAC) >>
         simp[]) >>
      `runtime_consistent env cx capture_st` by
        (drule_all eval_expr_results_preserves_runtime_consistent_from_eval >>
         disch_then ACCEPT_TAC) >>
      `valid_horizon cx initial_st H capture_st.storage_trace` by
        (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
         pure_rewrite_tac[valid_horizon_def] >> strip_tac >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `bind _ capture_cont prefix_st = _` mp_tac >>
      qpat_assum `eval_expr_results _ _ prefix_st = _`
        (fn th => pure_rewrite_tac[bind_def, th]) >>
      reverse (Cases_on `capture_res`) >> simp_tac(srw_ss())[raise_def]
      >- (strip_tac >> qpat_x_assum `capture_st = st'` SUBST_ALL_TAC >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      rename1 `eval_expr_results _ _ prefix_st = (INL results,capture_st)` >>
      qpat_x_assum `!v. storage_trace_frame (capture_cont v)` kall_tac >>
      simp_tac bool_ss [Abbr `capture_cont`, Once bind_apply] >>
      Cases_on `read_results cx results capture_st` >>
      rename1 `read_results cx results capture_st = (read_res,read_st)` >>
      drule read_results_state >> disch_then SUBST_ALL_TAC >>
      reverse (Cases_on `read_res`) >>
      simp_tac bool_ss [pairTheory.pair_case_def, sumTheory.sum_case_def, pairTheory.PAIR_EQ]
      >- (strip_tac >> qpat_x_assum `capture_st = st'` SUBST_ALL_TAC >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      rename1 `read_results cx results capture_st = (INL args,capture_st)` >>
      qpat_x_assum `!s prefix t s1 results t1 s2 args t2. eval_exprs _ _ _ = _ /\ _ ==> _`
        (qspecl_then [`st`,`prefix`,`prefix_st`,`prefix_st`,`results`,
                      `capture_st`,`capture_st`,`args`,`capture_st`]
          (mp_tac o SIMP_RULE (srw_ss()) [])) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
      qmatch_goalsub_abbrev_tac
        `bind (eval_exprs cx (DROP (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es))) salt_cont` >>
      `!v. storage_trace_frame (salt_cont v)` by
        simp[Abbr `salt_cont`, storage_trace_frame_create] >>
      Cases_on `eval_exprs cx (DROP (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)) capture_st` >>
      rename1 `eval_exprs _ _ capture_st = (salt_res,salt_st)` >>
      disch_tac >>
      `?delta. st'.storage_trace = salt_st.storage_trace ++ delta` by
        (qpat_x_assum `bind _ salt_cont capture_st = _` mp_tac >>
         qpat_assum `eval_exprs _ _ capture_st = _`
           (fn th => pure_rewrite_tac[bind_def, th]) >>
         Cases_on `salt_res` >> simp_tac(srw_ss())[raise_def] >> strip_tac
         >- (irule (INST_TYPE [alpha |-> ``:eval_result``] storage_trace_frame_prefix) >>
             goal_assum (drule_at Any) >> simp[]) >>
         qpat_x_assum `salt_st = st'` SUBST_ALL_TAC >>
         qexists `[]` >> simp_tac(srw_ss())[]) >>
      `IS_SOME salt_st.outcomes /\
       storage_well_formed_on cx salt_st (FST H) /\
       storage_observations_ok cx H salt_st.storage_trace` by
        (qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (TAKE 2 es) /\ _ ==> _` kall_tac >>
         qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (TAKE (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)) /\ _ ==> _` kall_tac >>
         irule (INST_TYPE [alpha |-> ``:value list + vyperState$exception``]
           recursive_prefix_handoff) >>
         qexistsl [`eval_exprs cx (DROP (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es))`,
                   `st'`,`salt_res`,`selected`,`capture_st`] >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             qpat_x_assum `!initial_st selected env st res st'. _`
               (qspecl_then [`initial_st`,`selected`,`env`,`capture_st`,`r`,`mid`] mp_tac) >>
             disch_then irule >>
             pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
             rpt conj_tac >>
             prefix_assumption_tac) >>
         conj_tac
         >- (mp_tac (cj 6 eval_outcomes_suffix_mutual) >>
             simp_tac(srw_ss())[outcomes_suffix_def] >>
             metis_tac[pairTheory.SND]) >>
         simp[]) >>
      `valid_horizon cx initial_st H salt_st.storage_trace` by
        (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
         pure_rewrite_tac[valid_horizon_def] >> strip_tac >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `bind _ salt_cont capture_st = _` mp_tac >>
      qpat_assum `eval_exprs _ _ capture_st = _`
        (fn th => pure_rewrite_tac[bind_def, th]) >>
      reverse (Cases_on `salt_res`) >> simp_tac(srw_ss())[raise_def]
      >- (strip_tac >> qpat_x_assum `salt_st = st'` SUBST_ALL_TAC >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `!v. storage_trace_frame (salt_cont v)` kall_tac >>
      simp_tac(srw_ss())[Abbr `salt_cont`] >> strip_tac >>
      qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (TAKE 2 es) /\ _ ==> _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (TAKE (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)) /\ _ ==> _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (DROP (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)) /\ _ ==> _` kall_tac >>
      qpat_x_assum `!cx initial_st st kind has_salt rof arg_tys vs blueprint_size res out selected. _` irule >>
      goal_assum (drule_at (Pat `eval_create _ _ _ _ _ _ _ _ = _`)) >>
      qexistsl [`initial_st`,`selected`] >> simp[] >>
      qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
      qpat_x_assum `selected = _` SUBST_ALL_TAC >> simp[]) >>
  strip_tac >> qpat_x_assum `prefix_st = st'` SUBST_ALL_TAC >>
  qpat_x_assum `!s prefix t. eval_exprs _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!s prefix t s1 results t1 s2 args t2. eval_exprs _ _ _ = _ /\ _ ==> _` kall_tac >>
  qpat_x_assum `!v. storage_trace_frame (prefix_cont v)` kall_tac >>
  qpat_x_assum `Abbrev _` kall_tac >>
  first_x_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then irule >> simp[] >>
  conj_tac >- (qexists `env` >> simp[]) >>
  qexistsl [`initial_st`,`selected`] >> simp[] >>
  qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
  qpat_x_assum `selected = _` SUBST_ALL_TAC >> simp[]
QED

Resume finite_prefix_Expr_Call_CreateTarget[PrefixBlueprint]:
  markerLib.RESUME_TAC >>
  rule_assum_tac (SIMP_RULE bool_ss
    [vyperASTTheory.create_kind_11, vyperASTTheory.create_kind_distinct]) >>
  `well_typed_exprs env (TAKE (if has_salt then 4 else 3) es) /\
   well_typed_exprs env (DROP (if has_salt then 4 else 3) es)` by
    metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE (if has_salt then 4 else 3) es)) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (if has_salt then 4 else 3) es))` by
    metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  pure_rewrite_tac[Once evaluate_def] >> simp_tac(srw_ss())[LET_THM] >>
  qmatch_goalsub_abbrev_tac
    `bind (eval_exprs cx (TAKE (if has_salt then 4 else 3) es)) prefix_cont` >>
  `!v. storage_trace_frame (prefix_cont v)` by
    (simp[Abbr `prefix_cont`] >> gen_tac >>
     irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_check_create_blueprint] >> gen_tac >>
     irule storage_trace_frame_bind_all >>
     simp[cj 11 evaluate_storage_trace_frame] >> gen_tac >>
     irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_results, storage_trace_frame_create]) >>
  Cases_on `eval_exprs cx (TAKE (if has_salt then 4 else 3) es) st` >>
  rename1 `eval_exprs _ _ st = (prefix_res,prefix_st)` >>
  qpat_assum `eval_exprs _ _ st = _`
    (fn th => pure_rewrite_tac[bind_def, th]) >>
  Cases_on `prefix_res` >> simp_tac(srw_ss())[raise_def]
  >- (rename1 `eval_exprs _ _ st = (INL prefix,prefix_st)` >> disch_tac >>
      `?delta. st'.storage_trace = prefix_st.storage_trace ++ delta` by
        (irule (INST_TYPE [alpha |-> ``:eval_result``] storage_trace_frame_prefix) >>
         goal_assum (drule_at Any) >> simp[]) >>
      `IS_SOME prefix_st.outcomes /\
       storage_well_formed_on cx prefix_st (FST H) /\
       storage_observations_ok cx H prefix_st.storage_trace` by
        (qpat_x_assum `!s prefix t s1 code_size t1. eval_exprs _ _ _ = _ /\ _ ==> _` kall_tac >>
         irule (INST_TYPE [alpha |-> ``:value list + vyperState$exception``]
           recursive_prefix_handoff) >>
         qexistsl [`eval_exprs cx (TAKE (if has_salt then 4 else 3) es)`,
                   `st'`,`INL prefix`,`selected`,`st`] >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             qpat_x_assum `!initial_st selected env st res st'. _`
               (qspecl_then [`initial_st`,`selected`,`env`,`st`,`r`,`mid`] mp_tac) >>
             disch_then irule >> rpt conj_tac >>
             prefix_assumption_tac) >>
         conj_tac
         >- (mp_tac (cj 6 eval_outcomes_suffix_mutual) >>
             simp_tac(srw_ss())[outcomes_suffix_def] >>
             metis_tac[pairTheory.SND]) >>
         simp[]) >>
      `runtime_consistent env cx prefix_st` by
        (drule_all eval_exprs_preserves_runtime_consistent >> disch_then ACCEPT_TAC) >>
      `valid_horizon cx initial_st H prefix_st.storage_trace` by
        (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
         pure_rewrite_tac[valid_horizon_def] >> strip_tac >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `!v. storage_trace_frame (prefix_cont v)` kall_tac >>
      qpat_x_assum `prefix_cont prefix prefix_st = _` mp_tac >>
      simp_tac bool_ss [Abbr `prefix_cont`, Once bind_apply] >>
      Cases_on `check_create_blueprint has_salt prefix prefix_st` >>
      rename1 `check_create_blueprint _ _ prefix_st = (gate_res,gate_st)` >>
      `gate_st = prefix_st` by
        (qpat_assum `check_create_blueprint _ _ _ = _`
           (mp_tac o Q.AP_TERM `SND`) >> simp[]) >>
      qpat_x_assum `gate_st = prefix_st` SUBST_ALL_TAC >>
      reverse (Cases_on `gate_res`) >>
      simp_tac bool_ss [pairTheory.pair_case_def, sumTheory.sum_case_def, pairTheory.PAIR_EQ]
      >- (strip_tac >> qpat_x_assum `prefix_st = st'` SUBST_ALL_TAC >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      rename1 `check_create_blueprint _ _ prefix_st = (INL code_size,prefix_st)` >>
      qpat_x_assum `!s prefix t s1 code_size t1. eval_exprs _ _ _ = _ /\ _ ==> _`
        (qspecl_then [`st`,`prefix`,`prefix_st`,`prefix_st`,`code_size`,`prefix_st`]
          (mp_tac o SIMP_RULE (srw_ss()) [])) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
      qmatch_goalsub_abbrev_tac
        `bind (eval_expr_results cx (DROP (if has_salt then 4 else 3) es)) capture_cont` >>
      `!v. storage_trace_frame (capture_cont v)` by
        (simp[Abbr `capture_cont`] >> gen_tac >>
         irule storage_trace_frame_bind_all >>
         simp[storage_trace_frame_read_results, storage_trace_frame_create]) >>
      Cases_on `eval_expr_results cx (DROP (if has_salt then 4 else 3) es) prefix_st` >>
      rename1 `eval_expr_results _ _ prefix_st = (capture_res,capture_st)` >>
      disch_tac >>
      `?delta. st'.storage_trace = capture_st.storage_trace ++ delta` by
        (qpat_x_assum `bind _ capture_cont prefix_st = _` mp_tac >>
         qpat_assum `eval_expr_results _ _ prefix_st = _`
           (fn th => pure_rewrite_tac[bind_def, th]) >>
         Cases_on `capture_res` >> simp_tac(srw_ss())[raise_def] >> strip_tac
         >- (irule (INST_TYPE [alpha |-> ``:eval_result``] storage_trace_frame_prefix) >>
             goal_assum (drule_at Any) >> simp[]) >>
         qpat_x_assum `capture_st = st'` SUBST_ALL_TAC >>
         qexists `[]` >> simp_tac(srw_ss())[]) >>
      `IS_SOME capture_st.outcomes /\
       storage_well_formed_on cx capture_st (FST H) /\
       storage_observations_ok cx H capture_st.storage_trace` by
        (qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (TAKE (if has_salt then 4 else 3) es) /\ _ ==> _` kall_tac >>
         irule (INST_TYPE [alpha |-> ``:eval_result list + vyperState$exception``]
           recursive_prefix_handoff) >>
         qexistsl [`eval_expr_results cx (DROP (if has_salt then 4 else 3) es)`,
                   `st'`,`capture_res`,`selected`,`prefix_st`] >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             qpat_x_assum `!initial_st selected env st res st'. _`
               (qspecl_then [`initial_st`,`selected`,`env`,`prefix_st`,`r`,`mid`] mp_tac) >>
             disch_then irule >>
             pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
             rpt conj_tac >>
             prefix_assumption_tac) >>
         conj_tac
         >- (rpt gen_tac >> strip_tac >>
             drule eval_expr_results_outcome_suffix >> disch_then ACCEPT_TAC) >>
         simp[]) >>
      `valid_horizon cx initial_st H capture_st.storage_trace` by
        (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
         pure_rewrite_tac[valid_horizon_def] >> strip_tac >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `bind _ capture_cont prefix_st = _` mp_tac >>
      qpat_assum `eval_expr_results _ _ prefix_st = _`
        (fn th => pure_rewrite_tac[bind_def, th]) >>
      reverse (Cases_on `capture_res`) >> simp_tac(srw_ss())[raise_def]
      >- (strip_tac >> qpat_x_assum `capture_st = st'` SUBST_ALL_TAC >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      rename1 `eval_expr_results _ _ prefix_st = (INL results,capture_st)` >>
      qpat_x_assum `!v. storage_trace_frame (capture_cont v)` kall_tac >>
      simp_tac(srw_ss())[Abbr `capture_cont`, bind_apply] >>
      Cases_on `read_results cx results capture_st` >>
      rename1 `read_results cx results capture_st = (read_res,read_st)` >>
      drule read_results_state >> disch_then SUBST_ALL_TAC >>
      reverse (Cases_on `read_res`) >> simp_tac(srw_ss())[]
      >- (strip_tac >> qpat_x_assum `capture_st = st'` SUBST_ALL_TAC >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >>
      qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (TAKE (if has_salt then 4 else 3) es) /\ _ ==> _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st'. well_typed_exprs env (DROP (if has_salt then 4 else 3) es) /\ _ ==> _` kall_tac >>
      qpat_x_assum `!cx initial_st st kind has_salt rof arg_tys vs blueprint_size res out selected. _` irule >>
      goal_assum (drule_at (Pat `eval_create _ _ _ _ _ _ _ _ = _`)) >>
      qexistsl [`initial_st`,`selected`] >> simp[] >>
      qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
      qpat_x_assum `selected = _` SUBST_ALL_TAC >> simp[]) >>
  strip_tac >> qpat_x_assum `prefix_st = st'` SUBST_ALL_TAC >>
  qpat_x_assum `!s prefix t s1 code_size t1. eval_exprs _ _ _ = _ /\ _ ==> _` kall_tac >>
  qpat_x_assum `!v. storage_trace_frame (prefix_cont v)` kall_tac >>
  qpat_x_assum `Abbrev _` kall_tac >>
  first_x_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then irule >> simp[] >>
  conj_tac >- (qexists `env` >> simp[]) >>
  qexistsl [`initial_st`,`selected`] >> simp[] >>
  qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
  qpat_x_assum `selected = _` SUBST_ALL_TAC >> simp[]
QED

Finalise finite_prefix_Expr_Call_CreateTarget
