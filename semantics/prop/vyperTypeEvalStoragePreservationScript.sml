(* Storage preservation for the mutually recursive evaluator. *)

Theory vyperTypeEvalStoragePreservation
Ancestors
  pair list vyperAST vyperCreate vyperInterpreter vyperState vyperStorageBackend vyperStorageLayoutSafety
  vyperTypeSystem vyperTypeEnv vyperTypeInvariants vyperTypeValues vyperTypeCallGraph
  vyperEvalMisc vyperStatePreservation vyperScopePreservation
  vyperTypeCallStackSoundness vyperValue
  vyperTypeBuiltins vyperTypeExprResult vyperTypeExprSoundness vyperTypeEvalSoundness
  vyperTypeExtCallSoundness vyperTypeABI vyperTypeEnvPreservation vyperTypeStatePreservation
  vyperTypeStmtSoundness vyperTypeAssignContext vyperTypeStoragePreservation
  vyperTypeBindArguments vyperEvalOutcomeSuffix vyperCallOutcomeStorage vyperTypeArgFits
  vyperPlaceStoragePreservation vyperPlaceFrames vyperPlaceTyping
  vyperStoragePlaceProvenance
  vyperPlaceResultTyping vyperTargetPlaceWrite vyperAugAssignWriteSoundness
  vyperImmutableMetadataFrame[ignore_grammar]
  vyperCallOutcome[ignore_grammar]
  vyperTypeEvalCaseProofs vyperTypeEvalProofs
Libs
  wordsLib markerLib BasicProvers

(* Primitive nonreentrant-lock operations and their effect on storage. *)

Theorem acquire_nonreentrant_lock_eq:
  acquire_nonreentrant_lock addr slot is_view st =
    if lookup_storage (n2w slot)
         (lookup_transient_storage addr st.tStorage) = 1w then
      (INR (Error (RuntimeError "nonreentrant lock")),
       st with storage_trace := st.storage_trace ++ [StorageLock slot])
    else if is_view then
      (INL (),st with storage_trace := st.storage_trace ++ [StorageLock slot])
    else
      (INL (),
       st with <|tStorage updated_by
         update_transient_storage addr
           (update_storage (n2w slot) 1w
             (lookup_transient_storage addr st.tStorage));
         storage_trace := st.storage_trace ++ [StorageLock slot]|>)
Proof
  Cases_on `lookup_storage (n2w slot)
    (lookup_transient_storage addr st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  simp[acquire_nonreentrant_lock_def, ignore_bind_def, record_storage_event_def, bind_def, get_transient_storage_def,
       update_transient_def, return_def, raise_def]
QED

Theorem release_nonreentrant_lock_eq:
  release_nonreentrant_lock addr slot st =
    (INL (),
     st with <|tStorage updated_by
       update_transient_storage addr
         (update_storage (n2w slot) 0w
           (lookup_transient_storage addr st.tStorage));
       storage_trace := st.storage_trace ++ [StorageLock slot]|>)
Proof
  simp[release_nonreentrant_lock_def, ignore_bind_def, record_storage_event_def, bind_def, get_transient_storage_def,
       update_transient_def, return_def]
QED

Theorem acquire_nonreentrant_lock_frame:
  acquire_nonreentrant_lock addr slot is_view st = (res,st') ==>
  st'.accounts = st.accounts /\
  (!read_addr read_slot.
     read_addr <> addr \/ read_slot <> n2w slot ==>
     lookup_storage read_slot
       (lookup_transient_storage read_addr st'.tStorage) =
     lookup_storage read_slot
       (lookup_transient_storage read_addr st.tStorage))
Proof
  Cases_on `lookup_storage (n2w slot)
    (lookup_transient_storage addr st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  simp[acquire_nonreentrant_lock_eq,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmExecutionTheory.update_transient_storage_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> Cases_on `addr = read_addr` >>
  gvs[vfmExecutionTheory.update_transient_storage_def,
      vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem get_storage_stk_scopes[local]:
  get_storage (cx with stk updated_by f) (st with scopes := scopes) b =
  get_storage cx st b
Proof
  Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]
QED

Theorem contract_storage_well_formed_stk_scopes[local]:
  contract_storage_well_formed
    (cx with stk updated_by f) (st with scopes := scopes) <=>
  contract_storage_well_formed cx st
Proof
  simp[contract_storage_well_formed_def,
       vyperLookupStorageTheory.well_formed_storage_def,
       vyperLookupStorageTheory.storage_var_in_range_def,
       vyperStorageBackendTheory.get_storage_backend_eq,
       vyperStorageBackendTheory.get_storage_def,
       get_storage_stk_scopes]
QED

Theorem eval_expr_preserves_runtime_consistent:
  well_typed_expr env e /\ runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 5 eval_scc_type_sound_mutual))) >> simp[]
QED

Theorem eval_expr_success_result_typed[local]:
  well_typed_expr env e /\
  runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (INL tv,st') ==>
  eval_result_typed (env,cx,st') tv (Type (expr_type e))
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 5 eval_scc_type_sound_mutual))) >> simp[]
QED

Theorem eval_exprs_preserves_runtime_consistent:
  well_typed_exprs env es /\ runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) /\
  eval_exprs cx es st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 6 eval_scc_type_sound_mutual))) >> simp[]
QED
Theorem get_storage_logs[local]:
  get_storage cx (st with logs updated_by f) b = get_storage cx st b
Proof
  Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]
QED

Theorem contract_storage_well_formed_logs:
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx (st with logs updated_by f)
Proof
  simp[vyperStorageLayoutSafetyTheory.contract_storage_well_formed_def,
       vyperLookupStorageTheory.well_formed_storage_def,
       vyperLookupStorageTheory.storage_var_in_range_def,
       vyperStorageBackendTheory.get_storage_backend_eq,
       get_storage_logs]
QED

Theorem eval_expr_place_preserves_runtime_consistent:
  (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
  runtime_consistent env cx st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 1 (SPEC_ALL (cj 5 eval_scc_type_sound_mutual))]
QED

Theorem eval_base_place_preserves_runtime_consistent:
  type_place_target env bt = SOME vt /\ runtime_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 1 (SPEC_ALL (cj 7 eval_scc_type_sound_mutual))]
QED

Theorem eval_target_place_success_storage_type:
  well_typed_target env bt ty /\ runtime_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  eval_target_place cx bt st = (INL p,st') ==>
  eval_result_typed (env,cx,st') (PlaceR p) (Type ty)
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 8 eval_scc_type_sound_mutual))) >> simp[]
QED

Theorem eval_expr_success_storage_facts:
  well_typed_expr env e /\ runtime_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (INL pv,st') ==>
  runtime_consistent env cx st' /\
  eval_result_typed (env,cx,st') pv (Type (expr_type e)) /\
  live_memory_result st' pv
Proof
  strip_tac >>
  `runtime_consistent env cx st'` by
    (drule_all eval_expr_preserves_runtime_consistent >> simp[]) >>
  `eval_result_typed (env,cx,st') pv (Type (expr_type e))` by
    (drule_all eval_expr_success_result_typed >> simp[]) >>
  simp[] >> fs[runtime_consistent_def] >>
  drule_at (Pat `eval_expr _ _ _ = _`)
    (cj 3 (SPEC_ALL (cj 5 eval_scc_type_sound_mutual))) >>
  disch_then (qspec_then `env` mp_tac) >> simp[]
QED

Theorem run_raw_call_storage_frame[local]:
  protected_storage_calls_preserve cx /\ contract_storage_well_formed cx st /\
  run_raw_call cx flags callee calldata amount gas st.accounts st.tStorage =
    SOME result /\
  st'.accounts = FST (SND (SND result)) /\
  st'.tStorage = FST (SND (SND (SND result))) ==>
  contract_storage_well_formed cx st'
Proof
  PairCases_on `result` >> rpt strip_tac >> gvs[] >>
  drule_all protected_storage_calls_preserve_run_raw_call >> strip_tac >>
  irule contract_storage_well_formed_backends_frame >>
  first_x_assum (irule_at Any) >> gvs[]
QED

(* oracle_storage_ok covers the outcome a call or staticcall takes from the
   oracle, as for extcall (eval_ext_call_effects_storage_preserved). *)
Theorem eval_raw_call_preserves_contract_storage:
  protected_storage_calls_preserve cx /\ contract_storage_well_formed cx st /\
  oracle_storage_ok cx st /\
  eval_raw_call cx flags target_addr calldata amount gas st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  simp[eval_raw_call_def, frame_call_value_def, check_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, lift_option_def, get_accounts_def,
       get_transient_storage_def, update_accounts_def, update_transient_def,
       append_logs_def, update_pending_deletions_def, record_storage_backend_def, record_storage_event_def,
       return_def, raise_def, COND_RATOR,
       vfmTypesTheory.option_CASE_rator, vfmTypesTheory.prod_CASE_rator,
       vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[pairTheory.UNCURRY_RATOR, pairTheory.UNCURRY_EQ, combinTheory.C_THM,
      combinTheory.o_THM, AllCaseEqs(), COND_RATOR, bind_def, return_def,
      raise_def] >>~-
  ([`run_raw_call _ _ _ _ _ _ _ _ = SOME _`],
   irule run_raw_call_storage_frame >> simp[] >> metis_tac[]) >>~-
  ([`adopt_call_outcome _ _ _ = (INR _,_)`],
   imp_res_tac vyperCallOutcomeTheory.adopt_call_outcome_frame >> gvs[]) >>~-
  ([`take_delegate_outcome _ _ _ _ _ = (INL _,_)`,
    `adopt_call_outcome _ _ _ = (INL (),_)`],
   drule_all take_adopt_delegate_outcome_storage_suffix >> simp[]) >>~-
  ([`adopt_call_outcome _ _ _ = (INL (),_)`],
   drule_all take_adopt_call_outcome_storage_suffix >> simp[]) >>~-
  ([`take_delegate_outcome _ _ _ _ _ = _`],
   drule_all take_delegate_outcome_storage_suffix >> simp[]) >>
  drule_all take_call_outcome_storage_suffix >> simp[]
QED

Theorem transfer_value_storage_frame[local]:
  transfer_value fromAddr toAddr amount st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >>
  qpat_x_assum `transfer_value _ _ _ _ = _` mp_tac >>
  Cases_on `amount = 0 ∨ fromAddr = toAddr`
  >- gvs[transfer_value_def, return_def] >>
  simp[transfer_value_def, bind_apply, ignore_bind_apply,
       get_accounts_def, check_def, assert_def, update_accounts_def,
       return_def, raise_def] >>
  rpt IF_CASES_TAC >> gvs[return_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `b` >>
  simp[vyperStorageBackendTheory.get_storage_def,
       vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem transfer_value_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  transfer_value fromAddr toAddr amount st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >> simp[] >>
  metis_tac[transfer_value_storage_frame]
QED

Theorem run_ext_call_storage_frame[local]:
  protected_storage_calls_preserve cx /\ contract_storage_well_formed cx st /\
  run_ext_call cx.txn.target callee calldata value_opt gas st.accounts
    st.tStorage txp = SOME result /\
  st'.accounts = FST (SND (SND result)) /\
  st'.tStorage = FST (SND (SND (SND result))) ==>
  contract_storage_well_formed cx st'
Proof
  PairCases_on `result` >> rpt strip_tac >> gvs[] >>
  drule_all protected_storage_calls_preserve_run_ext_call >> strip_tac >>
  irule contract_storage_well_formed_backends_frame >>
  first_x_assum (irule_at Any) >> gvs[]
QED

Theorem eval_send_preserves_contract_storage:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  protected_storage_calls_preserve cx /\
  eval_send cx has_gas vs st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  Cases_on `vs` >- (simp[eval_send_def, raise_def] >> rw[] >> gvs[]) >>
  Cases_on `t` >- (simp[eval_send_def, raise_def] >> rw[] >> gvs[]) >>
  simp[eval_send_def, frame_call_value_def, bind_def, ignore_bind_def, type_check_def, assert_def,
       check_def, lift_option_type_def, lift_option_def, get_accounts_def,
       get_transient_storage_def, update_accounts_def, update_transient_def,
       append_logs_def, update_pending_deletions_def, record_storage_backend_def, record_storage_event_def,
       return_def, raise_def,
       COND_RATOR, vfmTypesTheory.option_CASE_rator,
       vfmTypesTheory.prod_CASE_rator, vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[pairTheory.UNCURRY_RATOR, pairTheory.UNCURRY_EQ, combinTheory.C_THM,
      combinTheory.o_THM, AllCaseEqs(), COND_RATOR, bind_def, return_def,
      raise_def, assert_def, adopt_call_outcome_INR] >>~-
  ([`run_ext_call _ _ _ _ _ _ _ _ = SOME _`],
   irule run_ext_call_storage_frame >> simp[] >> metis_tac[]) >>
  metis_tac[take_call_outcome_storage_suffix,
            take_adopt_call_outcome_storage_suffix]
QED

(* Balance transfer/burning and deferred deletion leave protected storage
   unchanged, whether the message halts or the transfer check fails. *)
Theorem selfdestruct_tail_preserves_contract_storage:
  contract_storage_well_formed cx st /\
  (do
     transfer_value cx.txn.target target
       (lookup_account cx.txn.target st.accounts).balance;
     (if cx.txn.created_in_tx then do
        update_accounts (\acc. update_account cx.txn.target
          (lookup_account cx.txn.target acc with balance := 0) acc);
        update_pending_deletions (CONS cx.txn.target)
      od else return ());
     raise HaltException
   od) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  simp[ignore_bind_def, bind_def] >>
  qmatch_goalsub_abbrev_tac `transfer_value _ _ amount st` >>
  Cases_on `transfer_value cx.txn.target target amount st` >>
  rename1 `_ = (tres,mid)` >> strip_tac >>
  `contract_storage_well_formed cx mid` by
    metis_tac[transfer_value_preserves_contract_storage_well_formed] >>
  Cases_on `tres` >> gvs[] >>
  Cases_on `cx.txn.created_in_tx` >>
  gvs[bind_def, ignore_bind_def, update_accounts_def,
      update_pending_deletions_def, return_def, raise_def] >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `mid` >> simp[] >>
  gen_tac >> Cases_on `b` >>
  simp[vyperStorageBackendTheory.get_storage_def,
       vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[combinTheory.APPLY_UPDATE_THM]
QED

Theorem contract_storage_well_formed_stk:
  contract_storage_well_formed (cx with stk updated_by f) st <=>
  contract_storage_well_formed cx st
Proof
  `st with scopes := st.scopes = st` by
    gvs[evaluation_state_component_equality] >>
  mp_tac (Q.INST [`scopes` |-> `st.scopes`]
    contract_storage_well_formed_stk_scopes) >>
  asm_rewrite_tac[]
QED


Theorem oracle_storage_ok_stk[simp]:
  oracle_storage_ok (cx with stk updated_by f) st <=> oracle_storage_ok cx st
Proof
  simp[oracle_storage_ok_def, contract_storage_well_formed_stk]
QED
