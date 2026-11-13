(* Oracle primitives preserve a fixed horizon using only the already-valid
 * prefix before an outcome, never goodness of their completed trace. *)
Theory guardSourceCallPrimitives
Ancestors
  guardSourceInstrumentation vyperInterpreter vyperCreate vyperStorageTrace
  vyperCallOutcome vyperCallOutcomeProps vyperStorageFootprint vyperState

Theorem take_create_as_request[local]:
  take_create_outcome kind value initcode st = (INL (rq,co),mid) ==>
  take_request_outcome rq st = (INL (rq,co),mid) /\
  rq.cr_accounts = st.accounts /\ rq.cr_tStorage = st.tStorage
Proof
  strip_tac >> drule take_create_outcome_success >> strip_tac >>
  simp[take_request_outcome_def] >>
  gvs[extCallOracleTheory.record_request_def,
      extCallOracleTheory.computed_precompile_def, create_outcome_request_def]
QED

Theorem record_outcome_finite_prefix[local]:
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st.storage_trace ==>
  storage_well_formed_on cx
    (st with <|outcomes := os; requests := rqs;
               storage_trace := st.storage_trace ++ [StorageOutcome rq co]|>) (FST H) /\
  storage_observations_ok cx H (st.storage_trace ++ [StorageOutcome rq co])
Proof
  gvs[storage_observations_ok_append, storage_observations_ok_def,
      storage_trace_backends_well_formed_def, storage_trace_regions_def,
      storage_trace_locks_def, storage_roots_fit_def] >>
  gvs[storage_well_formed_on_def] >>
  rpt strip_tac >> first_x_assum drule >>
  Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]
QED

Theorem take_request_outcome_finite_prefix[local]:
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st.storage_trace /\
  take_request_outcome rq st = (res,mid) ==>
  storage_well_formed_on cx mid (FST H) /\
  storage_observations_ok cx H mid.storage_trace
Proof
  Cases_on `st.outcomes`
  >- (simp[take_request_outcome_def] >> metis_tac[]) >>
  simp[take_request_outcome_def] >> pairarg_tac >>
  strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[record_outcome_finite_prefix, storage_observations_ok_append]
QED

Theorem take_adopt_request_selected_prefix[local]:
  valid_horizon cx initial_st H st.storage_trace /\
  storage_well_formed_on cx st (FST H) /\
  rq0.cr_accounts = st.accounts /\ rq0.cr_tStorage = st.tStorage /\
  take_request_outcome rq0 st = (INL (rq,co),mid) /\
  adopt_call_outcome rq co mid = (res,out) /\
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
  storage_observations_ok cx H out.storage_trace
Proof
  strip_tac >>
  `?delta. out.storage_trace = mid.storage_trace ++ delta` by
    (drule vyperRequestTraceTheory.adopt_call_outcome_recorded_count >>
     simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `?suffix. selected = st.storage_trace ++ StorageOutcome rq co :: suffix` by
    (drule take_request_outcome_success >> strip_tac >> gvs[] >>
     qexists `delta ++ sfx` >> simp[]) >>
  `storage_well_formed_on cx out (FST H) /\
   valid_horizon cx initial_st H out.storage_trace` by
    (irule take_adopt_request_finite_prefix >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[valid_horizon_def]
QED

Theorem eval_ext_call_effects_finite_prefix:
  IS_SOME st.outcomes /\
  valid_horizon cx initial_st H st.storage_trace /\
  storage_well_formed_on cx st (FST H) /\
  eval_ext_call_effects cx target calldata value_opt gas accounts st = (res,out) /\
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
  storage_observations_ok cx H out.storage_trace
Proof
  Cases_on `st.outcomes` >> simp[] >> strip_tac >>
  qpat_x_assum `eval_ext_call_effects _ _ _ _ _ _ _ = _` mp_tac >>
  simp[eval_ext_call_effects_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, take_call_outcome_def] >>
  Cases_on `take_request_outcome (call_outcome_request target calldata value_opt st) st` >>
  rename1 `take_request_outcome _ st = (rr,mid)` >>
  reverse (Cases_on `rr`)
  >- (simp[raise_def] >> strip_tac >> gvs[] >>
      irule take_request_outcome_finite_prefix >>
      goal_assum (drule_at Any) >> gvs[valid_horizon_def]) >>
  rename1 `take_request_outcome _ _ = (INL taken,mid)` >>
  PairCases_on `taken` >>
  simp[ignore_bind_def, bind_def, return_def] >>
  Cases_on `taken1.co_success`
  >- (simp[] >>
      Cases_on `adopt_call_outcome taken0 taken1 mid` >>
      rename1 `adopt_call_outcome taken0 taken1 mid = (ar,after)` >>
      drule adopt_call_outcome_frame >> strip_tac >> gvs[] >>
      simp[bind_def, return_def] >> strip_tac >> gvs[] >>
      irule take_adopt_request_selected_prefix >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      simp[call_outcome_request_def] >> metis_tac[]) >>
  simp[raise_def] >> strip_tac >> gvs[] >>
  irule take_request_outcome_finite_prefix >>
  goal_assum (drule_at Any) >> gvs[valid_horizon_def]
QED

Theorem eval_send_finite_prefix:
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
  storage_observations_ok cx H out.storage_trace
Proof
  Cases_on `vs` >- (simp[eval_send_def, raise_def] >> rpt strip_tac >> gvs[valid_horizon_def]) >>
  Cases_on `t` >- (simp[eval_send_def, raise_def] >> rpt strip_tac >> gvs[valid_horizon_def]) >>
  Cases_on `st.outcomes` >> simp[] >> strip_tac >>
  qpat_x_assum `eval_send _ _ _ _ = _` mp_tac >>
  simp[eval_send_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, lift_option_type_def, lift_option_def,
       return_def, raise_def, AllCaseEqs()] >>
  strip_tac >>
  gvs[vfmTypesTheory.option_CASE_rator, vfmTypesTheory.prod_CASE_rator,
      vfmTypesTheory.sum_CASE_rator, pairTheory.UNCURRY_RATOR,
      AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac frame_call_value_state >> gvs[bind_def, return_def] >>
  gvs[AllCaseEqs(), take_call_outcome_def, check_def, assert_def,
      bind_def, ignore_bind_def, return_def, raise_def] >>
  all_tac >>~-
  ([`take_request_outcome _ _ = (INR _,_)`],
   irule take_request_outcome_finite_prefix >>
   goal_assum (drule_at Any) >> gvs[valid_horizon_def]) >>~-
  ([`take_request_outcome _ _ = (INL _,_)`],
   rename1 `take_request_outcome _ _ = (INL taken,mid)` >>
   PairCases_on `taken` >>
   gvs[assert_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
   imp_res_tac adopt_call_outcome_frame >> gvs[] >>~-
   ([`adopt_call_outcome _ _ _ = _`],
    irule take_adopt_request_selected_prefix >>
    goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
    simp[call_outcome_request_def] >> metis_tac[]) >>
   irule take_request_outcome_finite_prefix >>
   goal_assum (drule_at Any) >> gvs[valid_horizon_def]) >>
  gvs[valid_horizon_def]
QED

Theorem eval_ext_call_finite_prefix:
  IS_SOME st.outcomes /\
  valid_horizon cx initial_st H st.storage_trace /\
  storage_well_formed_on cx st (FST H) /\
  eval_ext_call cx static_flag skip_check sig_info opts vs st = (res,out) /\
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
  storage_observations_ok cx H out.storage_trace
Proof
  PairCases_on `sig_info` >> Cases_on `vs`
  >- (simp[eval_ext_call_def, raise_def] >> rpt strip_tac >> gvs[valid_horizon_def]) >>
  strip_tac >>
  qpat_x_assum `eval_ext_call _ _ _ _ _ _ _ = _` mp_tac >>
  simp[eval_ext_call_def, bind_def, ignore_bind_def, type_check_def,
       check_def, assert_def, lift_option_type_def, lift_option_def,
       get_accounts_def, return_def, raise_def, COND_RATOR,
       vfmTypesTheory.option_CASE_rator, vfmTypesTheory.prod_CASE_rator,
       vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[pairTheory.UNCURRY_RATOR, pairTheory.UNCURRY_EQ, combinTheory.C_THM,
      combinTheory.o_THM, AllCaseEqs(), COND_RATOR, bind_def, return_def,
      raise_def, lift_sum_runtime_def, lift_sum_def, check_def, assert_def] >>
  gvs[vfmTypesTheory.sum_CASE_rator, vfmTypesTheory.option_CASE_rator,
      AllCaseEqs(), return_def, raise_def, get_accounts_def] >>
  imp_res_tac frame_call_value_state >> gvs[] >>~-
  ([`eval_ext_call_effects _ _ _ _ _ _ _ = _`],
   irule eval_ext_call_effects_finite_prefix >>
   goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[valid_horizon_def]
QED

Theorem eval_raw_call_finite_prefix:
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
  storage_observations_ok cx H out.storage_trace
Proof
  Cases_on `st.outcomes` >> simp[] >> strip_tac >>
  qpat_x_assum `eval_raw_call _ _ _ _ _ _ _ = _` mp_tac >>
  simp[eval_raw_call_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, COND_RATOR,
       vfmTypesTheory.option_CASE_rator, vfmTypesTheory.prod_CASE_rator,
       vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  imp_res_tac frame_call_value_state >> gvs[] >>
  gvs[AllCaseEqs(), take_call_outcome_def, take_delegate_outcome_def,
      bind_def, ignore_bind_def, return_def, raise_def] >>
  all_tac >>~-
  ([`take_request_outcome _ _ = (INR _,_)`],
   irule take_request_outcome_finite_prefix >>
   goal_assum (drule_at Any) >> gvs[valid_horizon_def]) >>~-
  ([`take_request_outcome _ _ = (INL _,_)`],
   rename1 `take_request_outcome _ _ = (INL taken,mid)` >>
   PairCases_on `taken` >>
   gvs[bind_def, return_def, raise_def, AllCaseEqs()] >>
   imp_res_tac adopt_call_outcome_frame >> gvs[] >>
   gvs[COND_RATOR, bind_def, return_def, raise_def, AllCaseEqs()] >>
   irule take_adopt_request_selected_prefix >>
   goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
   simp[call_outcome_request_def, delegate_outcome_request_def] >> metis_tac[]) >>
  gvs[valid_horizon_def]
QED

Theorem take_create_outcome_finite_prefix[local]:
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st.storage_trace /\
  take_create_outcome kind value initcode st = (res,mid) ==>
  storage_well_formed_on cx mid (FST H) /\
  storage_observations_ok cx H mid.storage_trace
Proof
  Cases_on `st.outcomes`
  >- (simp[take_create_outcome_def] >> metis_tac[]) >>
  simp[take_create_outcome_def] >> pairarg_tac >>
  strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[record_outcome_finite_prefix, storage_observations_ok_append]
QED

Theorem create_oracle_result_finite_prefix[local]:
  valid_horizon cx initial_st H st.storage_trace /\
  storage_well_formed_on cx st (FST H) /\
  create_oracle_result salt value code rof st = (res,out) /\
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
  storage_observations_ok cx H out.storage_trace
Proof
  simp[create_oracle_result_def] >> strip_tac >> gvs[AllCaseEqs()] >>~-
  ([`take_create_outcome _ _ _ _ = (INL _,_)`],
      drule take_create_as_request >> strip_tac >>
      Cases_on `adopt_call_outcome rq outcome st'` >>
      rename1 `adopt_call_outcome rq outcome st' = (ar,after)` >>
      drule adopt_call_outcome_frame >> strip_tac >>
      gvs[AllCaseEqs()] >>
      irule take_adopt_request_selected_prefix >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule take_create_outcome_finite_prefix >>
  goal_assum (drule_at Any) >> gvs[valid_horizon_def]
QED

Theorem eval_create_finite_prefix:
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
  storage_observations_ok cx H out.storage_trace
Proof
  Cases_on `st.outcomes` >> simp[] >> strip_tac >>
  qpat_x_assum `eval_create _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[eval_create_def, bind_def, ignore_bind_def,
       lift_option_type_def, lift_option_def, get_accounts_def,
       check_def, assert_def, return_def, raise_def, COND_RATOR,
       vfmTypesTheory.option_CASE_rator, vfmTypesTheory.prod_CASE_rator,
       vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
  gvs[check_not_static_eq] >>~-
  ([`create_oracle_result _ _ _ _ _ = _`],
   irule create_oracle_result_finite_prefix >>
   goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[valid_horizon_def]
QED
