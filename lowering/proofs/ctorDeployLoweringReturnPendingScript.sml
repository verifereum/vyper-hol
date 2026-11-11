Theory ctorDeployLoweringReturnPending
Ancestors
  vyperState vyperStatePreservation vyperInterpreter vyperCallOutcomeFrame
  vyperPlaceFrames vyperStorageBackend option pair vyperMisc vyperMachineFrame
  supportedStmtTraverse supportedExprTraverse e2eDeployDefs vyperAST

Theorem pending_frame_bind:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) f /\
  (!v. state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) (g v)) ==>
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (vyperState$bind f g)
Proof
  strip_tac >> irule state_rel_frame_bind_guarded >> simp[] >> metis_tac[]
QED

Theorem pending_frame_state_preserving:
  (!st res st'. f st = (res,st') ==> st' = st) ==>
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) f
Proof
  simp[state_rel_frame_result] >> metis_tac[]
QED

Theorem pending_frame_reads:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (read_place cx p) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (read_result cx r) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (read_results cx rs) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (place_type_value cx p) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (lookup_global cx src nm) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (get_place r) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (extend_place cx r i) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (select_result cx ty pv sb) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (array_iterator_results cx ty res)
Proof
  rpt conj_tac >> irule pending_frame_state_preserving >>
  metis_tac[read_place_state, read_result_state, read_results_state,
    place_type_value_state, lookup_global_state, get_place_state,
    extend_place_state, select_result_state, array_iterator_results_state]
QED

Theorem pending_frame_primitives:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (return v) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (raise e) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (set_scopes scs) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (update_accounts fa) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (update_transient ft) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (set_immutable cx src nm ty value) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (write_storage_slot cx tr slot ty value)
Proof
  simp[state_rel_frame_def, return_def, raise_def, set_scopes_def,
    update_accounts_def, update_transient_def, set_immutable_def,
    set_address_immutables_def, get_address_immutables_def, write_storage_slot_def,
    get_storage_backend_def, set_storage_backend_def, bind_def,
    ignore_bind_def, get_accounts_def, get_transient_storage_def,
    lift_option_type_def, type_check_def, check_def, assert_def,
    AllCaseEqs()] >> rpt strip_tac >>
  rpt (BasicProvers.PURE_CASE_TAC >>
    gvs[return_def, raise_def, get_storage_backend_def,
      set_storage_backend_def, update_accounts_def, update_transient_def,
      bind_def, ignore_bind_def, AllCaseEqs()]) >>
  gvs[get_storage_backend_eq, set_storage_backend_eq,
      option_CASE_rator, prod_CASE_rator, COND_RATOR,
      return_def, raise_def, AllCaseEqs()] >>
  rpt (BasicProvers.PURE_CASE_TAC >>
    gvs[get_storage_backend_eq, set_storage_backend_eq, set_storage_def,
        return_def, raise_def, AllCaseEqs()]) >>
  qmatch_goalsub_abbrev_tac `set_storage _ _ backend _` >>
  Cases_on `backend` >> simp[set_storage_def]
QED

Theorem pending_frame_control:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (check b msg) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (type_check b msg) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    get_scopes /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (get_immutables cx src) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (lift_option_type opt msg) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (lift_sum z)
Proof
  simp[state_rel_frame_def, check_def, type_check_def, assert_def,
    get_scopes_def, get_immutables_def, get_address_immutables_def,
    lift_option_type_def, lift_sum_def, bind_def, return_def, raise_def,
    AllCaseEqs()] >> rpt strip_tac >>
  rpt (BasicProvers.PURE_CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem pending_frame_write_place:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (write_place cx p value)
Proof
  Cases_on `p` >> simp[write_place_def, pending_frame_primitives,
    ignore_bind_def] >>
  irule pending_frame_bind >> simp[pending_frame_control] >>
  gen_tac >> irule pending_frame_bind >> simp[pending_frame_control] >>
  simp[pairTheory.FORALL_PROD] >> rpt gen_tac >>
  simp[pending_frame_bind, pending_frame_control, pending_frame_primitives,
       pairTheory.FORALL_PROD]
QED

Theorem pending_frame_storage_read:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (get_storage_backend cx tr)
Proof
  simp[state_rel_frame_def, get_storage_backend_eq]
QED

Theorem pending_frame_pop_place:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (pop_place cx p)
Proof
  Cases_on `p` >>
  simp[pop_place_def, pending_frame_bind, pending_frame_control,
       pending_frame_primitives, pending_frame_storage_read,
       ignore_bind_def, pairTheory.FORALL_PROD]
  >~ [`pop_place cx (StoragePlace tr slot tv)`]
  >- (Cases_on `tv` >> simp[pop_place_def, pending_frame_primitives] >>
      rename1 `ArrayTV tv bd` >> Cases_on `bd` >>
      simp[pop_place_def, ignore_bind_def, pending_frame_primitives] >>
      rpt (irule pending_frame_bind >>
        simp[pending_frame_control, pending_frame_primitives,
             pending_frame_storage_read] >> rpt gen_tac)) >>
  rpt (irule pending_frame_bind >>
    simp[pending_frame_control, pending_frame_primitives,
         pairTheory.FORALL_PROD] >> rpt gen_tac)
QED

Theorem pending_frame_append_place:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (append_place cx p value)
Proof
  Cases_on `p` >>
  simp[append_place_def, pending_frame_bind, pending_frame_reads,
       pending_frame_control, pending_frame_write_place] >>
  rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
  simp[append_place_def, pending_frame_bind, pending_frame_reads,
       pending_frame_control, pending_frame_write_place] >>
  rename1 `ArrayTV tv bd` >> Cases_on `bd` >>
  simp[append_place_def, pending_frame_bind, pending_frame_reads,
       pending_frame_control, pending_frame_write_place,
       pending_frame_primitives, pending_frame_storage_read, ignore_bind_def]
QED

Theorem pending_frame_scope_handlers:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    push_scope /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    pop_scope /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (push_scope_with_var nm ty value) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (new_variable nm ty value) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (handle_loop_exception e) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    next_gas_reading /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (precompile_call_success bt)
Proof
  simp[state_rel_frame_def, push_scope_def, pop_scope_def,
    push_scope_with_var_def, new_variable_def, get_scopes_def, set_scopes_def,
    next_gas_reading_def, precompile_call_success_def,
    bind_def, ignore_bind_def, lift_option_type_def,
    check_def, type_check_def, assert_def, return_def, raise_def,
    AllCaseEqs()] >> rpt strip_tac >>
  rpt (BasicProvers.PURE_CASE_TAC >>
    gvs[return_def, raise_def, bind_def, handle_loop_exception_def,
        new_variable_def, set_scopes_def, AllCaseEqs()]) >>
  Cases_on `e` >> simp[handle_loop_exception_def, return_def, raise_def]
QED

Theorem pending_frame_transfer_lock:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (transfer_value sender target amount) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (acquire_nonreentrant_lock target slot view)
Proof
  simp[state_rel_frame_def, transfer_value_def,
    acquire_nonreentrant_lock_def, get_accounts_def, update_accounts_def,
    get_transient_storage_def, update_transient_def,
    bind_def, ignore_bind_def, return_def, raise_def, check_def,
    type_check_def, assert_def, AllCaseEqs()] >> rpt strip_tac >>
  rpt (BasicProvers.PURE_CASE_TAC >>
    gvs[return_def, raise_def, update_accounts_def, update_transient_def,
        get_accounts_def, get_transient_storage_def,
        bind_def, ignore_bind_def, check_def, assert_def, AllCaseEqs()])
QED

Theorem pending_frame_setup:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (send_call_value mut cx) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (lock_if_nr cx nr view)
Proof
  simp[send_call_value_def, lock_if_nr_def] >>
  Cases_on `cx.txn.value = 0` >> Cases_on `nr` >>
  simp[pending_frame_primitives, pending_frame_bind, pending_frame_control,
       pending_frame_transfer_lock, ignore_bind_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  simp[pending_frame_primitives, pending_frame_bind, pending_frame_control,
       pending_frame_transfer_lock, ignore_bind_def] >>
  Cases_on `view` >>
  simp[pending_frame_primitives, check_not_static_def, pending_frame_control,
       pending_frame_bind, pending_frame_transfer_lock]
QED

Theorem pending_frame_expression_reads:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    get_accounts /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (result_array_length cx r) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (conditional_result cx r) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (lift_option opt msg) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (lift_sum_runtime z)
Proof
  rpt conj_tac >> irule pending_frame_state_preserving >>
  metis_tac[get_accounts_state, result_array_length_state,
            conditional_result_state, lift_option_state, lift_sum_runtime_state]
QED

Theorem pending_frame_result:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) f /\
  f st = (res,st') ==> st'.pending_deletions = st.pending_deletions
Proof
  simp[state_rel_frame_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[]
QED

Theorem pending_module_constants:
  !mods am am_c.
  evaluate_module_constants cx am addr mods = SOME am_c ==>
  am_c.pending_deletions = am.pending_deletions
Proof
  Induct >> simp[evaluate_module_constants_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[evaluate_module_constants_def, AllCaseEqs()] >> strip_tac >>
  first_x_assum drule >> simp[merge_constants_def]
QED

Theorem pending_all_constants:
  evaluate_all_constants cx am addr mods = SOME am_c ==>
  am_c.pending_deletions = am.pending_deletions
Proof
  rewrite_tac[evaluate_all_constants_def] >>
  strip_tac >> drule pending_module_constants >> simp[]
QED


Theorem pending_frame_bind_guarded:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) f /\
  (!s v t. f s = (INL v,t) ==>
    state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) (g v)) ==>
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (vyperState$bind f g)
Proof
  strip_tac >> irule state_rel_frame_bind_guarded >> simp[] >> metis_tac[]
QED

Theorem supported_fields_exists_map_snd:
  !fields. supported_fields_exists p fields = supported_exprs_exists p (MAP SND fields)
Proof
  Induct >> simp[supported_expr_exists_def] >>
  gen_tac >> PairCases_on `h` >> simp[supported_expr_exists_def]
QED

Theorem supported_exprs_absent_hd:
  es <> [] /\ ~supported_exprs_exists p es ==> ~supported_expr_exists p (HD es)
Proof
  Cases_on `es` >> simp[supported_expr_exists_def]
QED

Theorem pending_frame_flag_member:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (lookup_flag_mem cx nsid mid)
Proof
  irule pending_frame_state_preserving >> metis_tac[lookup_flag_mem_state]
QED

Theorem pending_frame_switch:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) f /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) g ==>
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (switch_BoolV cx tv f g)
Proof
  strip_tac >> simp[switch_BoolV_def] >>
  match_mp_tac pending_frame_bind >> conj_tac
  >- MATCH_ACCEPT_TAC (cj 2 pending_frame_reads) >>
  gen_tac >> BETA_TAC >> rpt IF_CASES_TAC >> simp[pending_frame_primitives]
QED

Theorem pending_call_free_expressions:
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==> T) /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==> T) /\
  (!cx it st res st'. eval_iterator cx it st = (res,st') ==> T) /\
  (!cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res,st') ==> T) /\
  (!cx e st res st'. ~supported_expr_exists constructor_call_root e /\
    eval_expr cx e st = (res,st') ==> st'.pending_deletions = st.pending_deletions) /\
  (!cx es st res st'. ~supported_exprs_exists constructor_call_root es /\
    eval_exprs cx es st = (res,st') ==> st'.pending_deletions = st.pending_deletions) /\
  (!cx target st res st'. ~supported_target_exists constructor_call_root target /\
    eval_base_place cx target st = (res,st') ==> st'.pending_deletions = st.pending_deletions) /\
  (!cx target st res st'. ~supported_target_exists constructor_call_root target /\
    eval_target_place cx target st = (res,st') ==> st'.pending_deletions = st.pending_deletions) /\
  (!cx target v st res st'. ~supported_assignment_exists constructor_call_root target /\
    assign_tuple_targets cx target v st = (res,st') ==> st'.pending_deletions = st.pending_deletions) /\
  (!cx targets vs st res st'. ~supported_assignments_exists constructor_call_root targets /\
    assign_tuple_target_list cx targets vs st = (res,st') ==> st'.pending_deletions = st.pending_deletions) /\
  (!cx es st res st'. ~supported_exprs_exists constructor_call_root es /\
    eval_expr_results cx es st = (res,st') ==> st'.pending_deletions = st.pending_deletions)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[] >>
  rpt strip_tac >>
  gvs[supported_expr_exists_def, supported_assignment_exists_def,
      constructor_call_root_def, supported_fields_exists_map_snd] >>
  qpat_x_assum `_ = (res,st')` mp_tac >>
  map_every qid_spec_tac [`st'`,`res`,`st`] >>
  CONV_TAC (HO_REWR_CONV (GSYM state_rel_frame_result)) >>
  simp_tac bool_ss [Once evaluate_def, ignore_bind_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp_tac bool_ss [pending_frame_primitives, pending_frame_control,
    pending_frame_reads, pending_frame_expression_reads, pending_frame_flag_member]
  >~ [`state_rel_frame _ (bind get_scopes _)`]
  >- simp[pending_frame_bind, pending_frame_primitives, pending_frame_control]
  >- (match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> BETA_TAC >>
      match_mp_tac pending_frame_bind >> conj_tac
      >- (irule pending_frame_switch >> conj_tac >>
          rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_expression_reads])
  >- (simp_tac bool_ss [LET_THM] >>
      match_mp_tac pending_frame_bind >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_primitives])
  >- (match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> BETA_TAC >>
      match_mp_tac pending_frame_bind >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_bind, pending_frame_reads])
  >- (match_mp_tac pending_frame_bind >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_reads])
  >- (match_mp_tac pending_frame_bind_guarded >> conj_tac
  >- simp[pending_frame_control] >>
  rpt strip_tac >> BETA_TAC >>
  match_mp_tac pending_frame_bind >> conj_tac
  >- (Cases_on `bt = Len`
      >- (gvs[] >>
          `es <> []` by
            (Cases_on `es` >>
             gvs[type_check_def, check_def, assert_def,
                 return_def, raise_def, vyperContextTheory.builtin_args_length_ok_def]) >>
          drule_all supported_exprs_absent_hd >> strip_tac >>
          match_mp_tac pending_frame_bind >> conj_tac
          >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
          simp[pending_frame_bind, pending_frame_expression_reads, pending_frame_primitives]) >>
      Cases_on `bt = Env MsgGas`
      >- gvs[pending_frame_scope_handlers] >>
      gvs[] >> IF_CASES_TAC >>
      match_mp_tac pending_frame_bind >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[])
      >- simp[pending_frame_bind, pending_frame_control]
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_bind, pending_frame_expression_reads, pending_frame_control,
           pending_frame_scope_handlers, pending_frame_primitives]) >>
  simp[pending_frame_primitives])
  >~ [`state_rel_frame _ (bind get_scopes _)`]
  >- simp[pending_frame_bind, pending_frame_control, pending_frame_primitives]
  >~ [`state_rel_frame _ (bind (eval_base_place _ _) get_place)`]
  >- (match_mp_tac pending_frame_bind >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_reads])
  >~ [`state_rel_frame _ (bind (eval_target_place _ _) (pop_place _))`]
  >- (match_mp_tac pending_frame_bind >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_pop_place])
  >~ [`extend_place _ _ (ValueSubscript _)`]
  >- (match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> BETA_TAC >>
      match_mp_tac pending_frame_bind >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_bind, pending_frame_reads])
  >~ [`value_CASE`]
  >- (Cases_on `v` >> simp[pending_frame_primitives] >>
      rename1 `array_value_CASE av _ _ _` >> Cases_on `av` >>
      simp[pending_frame_primitives] >>
      rewrite_tac[state_rel_frame_result] >> metis_tac[])
  >~ [`state_rel_frame _ (bind (eval_base_place _ _) (\pv. extend_place _ pv _))`]
  >- (match_mp_tac pending_frame_bind >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_reads])
  >~ [`state_rel_frame _ (bind (eval_expr _ _) (\tv. bind (read_result _ tv) _))`]
  >- (match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> BETA_TAC >>
      match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- simp[pending_frame_reads] >>
      rpt strip_tac >> BETA_TAC >>
      match_mp_tac pending_frame_bind >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_primitives])
  >~ [`state_rel_frame _ (bind (eval_expr _ _) _)`]
  >- (match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> BETA_TAC >>
      match_mp_tac pending_frame_bind >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_primitives])
  >~ [`write_place`]
  >- (match_mp_tac pending_frame_bind >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_write_place])
  >~ [`state_rel_frame _ (bind (type_check _ _) _)`]
  >- (match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- simp[pending_frame_control] >>
      rpt strip_tac >> Cases_on `v` >> BETA_TAC >>
      match_mp_tac pending_frame_bind >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_bind, pending_frame_control, pending_frame_primitives]) >>
  match_mp_tac pending_frame_bind_guarded >> conj_tac
  >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
  rpt strip_tac >> BETA_TAC >>
  rename1 `assign_tuple_targets _ _ _ _ = (INL u,_)` >> Cases_on `u` >>
  rewrite_tac[state_rel_frame_result] >> metis_tac[]
QED


Theorem pending_call_free_expression_frames:
  (~supported_expr_exists constructor_call_root e ==>
    state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) (eval_expr cx e)) /\
  (~supported_exprs_exists constructor_call_root es ==>
    state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) (eval_exprs cx es)) /\
  (~supported_target_exists constructor_call_root target ==>
    state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) (eval_target_place cx target)) /\
  (~supported_assignment_exists constructor_call_root assn ==>
    state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) (assign_tuple_targets cx assn v))
Proof
  rewrite_tac[state_rel_frame_result] >>
  metis_tac[pending_call_free_expressions]
QED

Theorem pending_frame_statement_primitives:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) (lift_option opt msg) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) (check_not_static cx) /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) (push_log ev)
Proof
  simp[check_not_static_def, pending_frame_control, state_rel_frame_def,
       push_log_def, lift_option_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `opt` >> simp[return_def, raise_def]
QED

Theorem pending_frame_try:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) f /\
  (!e. state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) (h e)) ==>
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) (try f h)
Proof
  strip_tac >> irule state_rel_frame_try >> simp[] >> metis_tac[]
QED

Theorem pending_frame_finally:
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) f /\
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) g ==>
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions) (finally f g)
Proof
  strip_tac >> irule state_rel_frame_finally >> simp[] >> metis_tac[]
QED

Theorem pending_custom_error_args_absent:
  EVERY ($~ o supported_expr_exists constructor_call_root) (custom_error_exprs err) /\
  order_custom_error_args params err = SOME es ==>
  ~supported_exprs_exists constructor_call_root es
Proof
  strip_tac >> drule order_custom_error_args_perm >> strip_tac >>
  gvs[supported_exprs_exists_every] >> metis_tac[sortingTheory.PERM_EVERY]
QED

Theorem pending_frame_custom_error_dispatch:
  EVERY ($~ o supported_expr_exists constructor_call_root) (custom_error_exprs err) ==>
  state_rel_frame (\(s:evaluation_state) t. t.pending_deletions = s.pending_deletions)
    (case err of CustomError id positional kwargs =>
      case get_module_code cx (FST id) of
        NONE => raise (Error (RuntimeError "custom error declaration"))
      | SOME tops => case lookup_custom_error_args_in (SND id) tops of
        NONE => raise (Error (RuntimeError "custom error declaration"))
      | SOME params => case order_custom_error_args params err of
        NONE => raise (Error (RuntimeError "custom error arguments"))
      | SOME es => bind (eval_exprs cx es) (\vs.
          bind (lift_option (build_custom_error_data (get_tenv cx) (SND id)
            (MAP SND params) vs) "custom error encoding")
          (\data. raise (Error (RevertData data)))))
Proof
  Cases_on `err` >> strip_tac >> simp[] >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[pending_frame_primitives] >>
  drule_all pending_custom_error_args_absent >> strip_tac >>
  simp[pending_frame_bind, pending_call_free_expression_frames,
       pending_frame_statement_primitives, pending_frame_primitives]
QED

Theorem pending_call_free_statements:
  (!cx s st res st'. ~supported_stmt_expr_exists constructor_call_root s /\
    eval_stmt cx s st = (res,st') ==> st'.pending_deletions = st.pending_deletions) /\
  (!cx ss st res st'. ~supported_stmts_expr_exists constructor_call_root ss /\
    eval_stmts cx ss st = (res,st') ==> st'.pending_deletions = st.pending_deletions) /\
  (!cx it st res st'. ~supported_iterator_exists constructor_call_root it /\
    eval_iterator cx it st = (res,st') ==> st'.pending_deletions = st.pending_deletions) /\
  (!cx tyv nm body vs st res st'. ~supported_stmts_expr_exists constructor_call_root body /\
    eval_for cx tyv nm body vs st = (res,st') ==> st'.pending_deletions = st.pending_deletions) /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==> T) /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==> T) /\
  (!cx t st res st'. eval_base_place cx t st = (res,st') ==> T) /\
  (!cx t st res st'. eval_target_place cx t st = (res,st') ==> T) /\
  (!cx t v st res st'. assign_tuple_targets cx t v st = (res,st') ==> T) /\
  (!cx ts vs st res st'. assign_tuple_target_list cx ts vs st = (res,st') ==> T) /\
  (!cx es st res st'. eval_expr_results cx es st = (res,st') ==> T)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[] >>
  rpt strip_tac >>
  gvs[supported_stmt_expr_exists_def, supported_iterator_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_expr_exists_def, supported_assignment_exists_def] >>
  qpat_x_assum `_ = (res,st')` mp_tac >>
  map_every qid_spec_tac [`st'`,`res`,`st`] >>
  CONV_TAC (HO_REWR_CONV (GSYM state_rel_frame_result)) >>
  simp_tac bool_ss [Once evaluate_def, ignore_bind_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[pending_frame_primitives, pending_frame_control,
    pending_frame_reads, pending_frame_expression_reads,
    pending_frame_custom_error_dispatch]
  >~ [`finally`]
  >- (match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- simp[pending_call_free_expression_frames] >>
      rpt strip_tac >> BETA_TAC >> match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- simp[pending_frame_scope_handlers] >>
      rpt strip_tac >> rename1 `push_scope _ = (INL u,_)` >>
      Cases_on `u` >> BETA_TAC >>
      irule pending_frame_finally >> conj_tac
      >- (irule pending_frame_switch >> conj_tac >>
          rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      simp[pending_frame_scope_handlers])
  >~ [`state_rel_frame _ (bind (eval_stmt _ _) _)`]
  >- (match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> rename1 `eval_stmt _ _ _ = (INL u,_)` >> Cases_on `u` >>
      BETA_TAC >> rewrite_tac[state_rel_frame_result] >> metis_tac[])
  >~ [`push_scope_with_var`]
  >- (match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- simp[pending_frame_reads] >>
      rpt strip_tac >> BETA_TAC >>
      match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- simp[pending_frame_scope_handlers] >>
      rpt strip_tac >> rename1 `push_scope_with_var _ _ _ _ = (INL u,_)` >>
      Cases_on `u` >> BETA_TAC >>
      match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- (irule pending_frame_finally >> conj_tac
          >- (match_mp_tac pending_frame_try >> conj_tac
              >- (match_mp_tac pending_frame_bind >> conj_tac
                  >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
                  simp[pending_frame_primitives]) >>
              simp[pending_frame_scope_handlers]) >>
          simp[pending_frame_scope_handlers]) >>
      rpt strip_tac >> BETA_TAC >> rename1 `if b then _ else _` >>
      Cases_on `b` >- simp[pending_frame_primitives] >>
      rewrite_tac[state_rel_frame_result] >>
      metis_tac[ignore_bind_def])
  >~ [`eval_for`]
  >- (match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- simp[pending_frame_control] >>
      rpt strip_tac >> BETA_TAC >>
      match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- (rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> BETA_TAC >>
      match_mp_tac pending_frame_bind_guarded >> conj_tac
      >- simp[pending_frame_control] >>
      rpt strip_tac >> rename1 `check _ _ _ = (INL u,_)` >> Cases_on `u` >>
      BETA_TAC >> rewrite_tac[state_rel_frame_result] >> metis_tac[]) >>
  simp[pending_frame_bind, pending_call_free_expression_frames,
    pending_frame_primitives, pending_frame_control, pending_frame_reads,
    pending_frame_scope_handlers, pending_frame_write_place, pending_frame_append_place,
    pending_frame_expression_reads, pending_frame_switch,
    pending_frame_statement_primitives, pending_frame_custom_error_dispatch]
  >~ [`switch_BoolV`]
  >- (match_mp_tac pending_frame_bind >> conj_tac
      >- simp[pending_call_free_expression_frames] >>
      gen_tac >> BETA_TAC >> irule pending_frame_switch >> conj_tac
      >- simp[pending_frame_primitives] >>
      simp[pending_frame_bind, pending_call_free_expression_frames,
           pending_frame_reads, pending_frame_control, pending_frame_primitives])
  >~ [`TupleTarget`]
  >- (match_mp_tac pending_frame_bind >> conj_tac
      >- simp[pending_call_free_expression_frames] >>
      gen_tac >> BETA_TAC >> match_mp_tac pending_frame_bind >> conj_tac
      >- simp[pending_frame_reads] >>
      simp[pending_call_free_expression_frames, supported_assignment_exists_def]) >>
  rpt (match_mp_tac pending_frame_bind >> conj_tac
       >- simp[pending_call_free_expression_frames, pending_frame_reads, pending_frame_control] >>
       gen_tac >> BETA_TAC) >>
  simp[pending_frame_primitives, pending_frame_write_place]

QED
