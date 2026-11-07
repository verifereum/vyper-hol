(* The observation log does not affect evaluation and retains every prefix. *)
Theory vyperStorageTrace
Ancestors
  vyperState vyperCallOutcome vyperCreate vyperInterpreter

Definition storage_trace_frame_def:
  storage_trace_frame (f : evaluation_state -> 'a evaluation_result) <=>
    !st observations.
      f (st with storage_trace := observations) =
      case f (st with storage_trace := []) of
        (res,st') =>
          (res,st' with storage_trace := observations ++ st'.storage_trace)
End

Theorem storage_trace_frame_action:
  storage_trace_frame f <=>
  !st p. f (st with storage_trace := p ++ st.storage_trace) =
    case f st of (r,t) => (r,t with storage_trace := p ++ t.storage_trace)
Proof
  eq_tac
  >- (pure_rewrite_tac[storage_trace_frame_def] >> strip_tac >> rpt gen_tac >>
      first_assum (qspecl_then [`st`, `p ++ st.storage_trace`] mp_tac) >>
      first_x_assum (qspecl_then [`st`, `st.storage_trace`] mp_tac) >>
      Cases_on `f (st with storage_trace := [])` >> simp[listTheory.APPEND_ASSOC])
  >> rw[storage_trace_frame_def] >>
  first_x_assum (qspecl_then [`st with storage_trace := []`, `observations`] mp_tac) >>
  simp[]
QED

Theorem storage_trace_frame_result:
  storage_trace_frame f /\ f st = (r,t) ==>
  f (st with storage_trace := p ++ st.storage_trace) =
    (r,t with storage_trace := p ++ t.storage_trace)
Proof
  simp[storage_trace_frame_action] >> metis_tac[]
QED

Theorem storage_trace_frame_unprefix:
  storage_trace_frame f /\
  f (st with storage_trace := p ++ st.storage_trace) = (r,t) ==>
  ?u. f st = (r,u) /\ t = u with storage_trace := p ++ u.storage_trace
Proof
  strip_tac >> Cases_on `f st` >>
  drule_all storage_trace_frame_result >>
  disch_then (qspec_then `p` mp_tac) >> simp[] >> strip_tac >> gvs[]
QED

Theorem storage_trace_frame_replace:
  storage_trace_frame f /\
  f (st with storage_trace := observations) = (r,t) ==>
  ?u. f st = (r,u) /\
      (t with storage_trace := []) = (u with storage_trace := [])
Proof
  pure_rewrite_tac[storage_trace_frame_def] >> strip_tac >>
  first_assum (qspecl_then [`st`, `observations`] mp_tac) >>
  first_x_assum (qspecl_then [`st`, `st.storage_trace`] mp_tac) >>
  Cases_on `f (st with storage_trace := [])` >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem storage_trace_frame_unprefix_sequence:
  storage_trace_frame f /\ storage_trace_frame g /\
  f (st with storage_trace := p ++ st.storage_trace) = (r,t) /\
  g t = (q,v) ==>
  ?u w. f st = (r,u) /\ g u = (q,w) /\
        v = w with storage_trace := p ++ w.storage_trace
Proof
  strip_tac >> drule_all storage_trace_frame_unprefix >> strip_tac >> gvs[] >>
  drule_all storage_trace_frame_unprefix >> strip_tac >> metis_tac[]
QED

Theorem abstract_machine_from_state_storage_trace:
  abstract_machine_from_state srcs exps layouts (st with storage_trace := observations) =
  abstract_machine_from_state srcs exps layouts st
Proof
  simp[abstract_machine_from_state_def]
QED

Theorem storage_trace_frame_return:
  storage_trace_frame (return v)
Proof
  simp[storage_trace_frame_def, return_def]
QED

Theorem storage_trace_frame_raise:
  storage_trace_frame (raise e)
Proof
  simp[storage_trace_frame_def, raise_def]
QED

Theorem storage_trace_frame_read:
  (!st p. h (st with storage_trace := p) = h st) ==>
  storage_trace_frame (\st. return (h st) st)
Proof
  simp[storage_trace_frame_def, return_def]
QED

Theorem storage_trace_frame_event:
  storage_trace_frame (record_storage_event ev)
Proof
  simp[storage_trace_frame_def, record_storage_event_def, return_def]
QED

Theorem storage_trace_frame_backend:
  storage_trace_frame record_storage_backend
Proof
  simp[storage_trace_frame_def, record_storage_backend_def,
       record_storage_event_def, return_def]
QED

Theorem storage_trace_frame_bind:
  storage_trace_frame f /\
  (!v. (?s t. f s = (INL v,t)) ==> storage_trace_frame (g v)) ==>
  storage_trace_frame (bind f g)
Proof
  strip_tac >> pure_rewrite_tac[storage_trace_frame_action] >> rpt gen_tac >>
  Cases_on `f st` >> rename1 `f st = (result,out)` >>
  drule_all storage_trace_frame_result >>
  disch_then (qspec_then `p` assume_tac) >>
  Cases_on `result` >> simp[bind_def] >>
  `storage_trace_frame (g x)` by metis_tac[] >>
  gvs[storage_trace_frame_action]
QED

Theorem storage_trace_frame_bind_all:
  storage_trace_frame f /\ (!v. storage_trace_frame (g v)) ==>
  storage_trace_frame (bind f g)
Proof
  metis_tac[storage_trace_frame_bind]
QED

Theorem storage_trace_frame_ignore_bind:
  storage_trace_frame f /\ storage_trace_frame g ==>
  storage_trace_frame (ignore_bind f g)
Proof
  strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
  irule storage_trace_frame_bind_all >> simp[]
QED

Theorem storage_trace_frame_try:
  storage_trace_frame f /\
  (!e. (?s t. f s = (INR e,t)) ==> storage_trace_frame (h e)) ==>
  storage_trace_frame (try f h)
Proof
  strip_tac >> pure_rewrite_tac[storage_trace_frame_action] >> rpt gen_tac >>
  Cases_on `f st` >> rename1 `f st = (result,out)` >>
  drule_all storage_trace_frame_result >>
  disch_then (qspec_then `p` assume_tac) >>
  Cases_on `result` >> simp[try_def] >>
  `storage_trace_frame (h y)` by metis_tac[] >>
  gvs[storage_trace_frame_action]
QED

Theorem storage_trace_frame_finally:
  storage_trace_frame f /\ storage_trace_frame g ==>
  storage_trace_frame (finally f g)
Proof
  strip_tac >> pure_rewrite_tac[storage_trace_frame_action] >> rpt gen_tac >>
  Cases_on `f st` >> rename1 `f st = (result,out)` >>
  drule_all storage_trace_frame_result >>
  disch_then (qspec_then `p` assume_tac) >>
  Cases_on `result` >> simp[finally_def] >>
  irule (iffLR storage_trace_frame_action) >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_return, storage_trace_frame_raise]
QED

Theorem storage_trace_frame_cond:
  storage_trace_frame f /\ storage_trace_frame g ==>
  storage_trace_frame (if b then f else g)
Proof
  Cases_on `b` >> simp[]
QED

Theorem storage_trace_frame_checks:
  storage_trace_frame (assert b e) /\
  storage_trace_frame (check b msg) /\
  storage_trace_frame (type_check b msg)
Proof
  simp[storage_trace_frame_def, assert_def, check_def, type_check_def]
QED

Theorem storage_trace_frame_lifts:
  storage_trace_frame (lift_option opt msg) /\
  storage_trace_frame (lift_option_type opt msg) /\
  storage_trace_frame (lift_sum sm) /\
  storage_trace_frame (lift_sum_runtime sr)
Proof
  Cases_on `opt` >> Cases_on `sm` >> Cases_on `sr` >>
  simp[lift_option_def, lift_option_type_def, lift_sum_def,
       lift_sum_runtime_def, storage_trace_frame_return, storage_trace_frame_raise]
QED

Theorem storage_trace_frame_state_reads:
  storage_trace_frame get_accounts /\
  storage_trace_frame get_transient_storage /\
  storage_trace_frame get_pending_deletions /\
  storage_trace_frame get_scopes
Proof
  simp[storage_trace_frame_def, get_accounts_def, get_transient_storage_def,
       get_pending_deletions_def, get_scopes_def, return_def]
QED

Theorem storage_trace_frame_state_updates:
  storage_trace_frame (update_accounts fa) /\
  storage_trace_frame (update_transient ft) /\
  storage_trace_frame (update_pending_deletions fp) /\
  storage_trace_frame (push_log lg) /\
  storage_trace_frame (append_logs ls) /\
  storage_trace_frame (set_scopes scs) /\
  storage_trace_frame push_scope /\
  storage_trace_frame (push_scope_with_var nm ty v) /\
  storage_trace_frame (set_address_immutables cx imms)
Proof
  simp[storage_trace_frame_def, update_accounts_def, update_transient_def,
       update_pending_deletions_def, push_log_def, append_logs_def,
       set_scopes_def, push_scope_def, push_scope_with_var_def,
       set_address_immutables_def, return_def]
QED

Theorem storage_trace_frame_pop_scope:
  storage_trace_frame pop_scope
Proof
  simp[storage_trace_frame_def, pop_scope_def, return_def, raise_def] >>
  gen_tac >> Cases_on `st.scopes` >> simp[]
QED

Theorem storage_trace_frame_get_storage_backend:
  storage_trace_frame (get_storage_backend cx transient)
Proof
  Cases_on `transient` >>
  simp[storage_trace_frame_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def, bind_def, return_def]
QED

Theorem storage_trace_frame_set_storage_backend:
  storage_trace_frame (set_storage_backend cx transient backend)
Proof
  Cases_on `transient` >>
  simp[storage_trace_frame_def, set_storage_backend_def,
       update_transient_def, update_accounts_def, get_accounts_def,
       bind_def, return_def]
QED

Theorem storage_trace_frame_read_storage_slot:
  storage_trace_frame (read_storage_slot cx transient slot ty)
Proof
  pure_rewrite_tac[read_storage_slot_def] >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_get_storage_backend, storage_trace_frame_lifts]
QED

Theorem storage_trace_frame_write_storage_slot:
  storage_trace_frame (write_storage_slot cx transient slot ty v)
Proof
  pure_rewrite_tac[write_storage_slot_def] >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_get_storage_backend] >> gen_tac >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_lifts, storage_trace_frame_set_storage_backend]
QED

Theorem storage_trace_frame_get_address_immutables:
  storage_trace_frame (get_address_immutables cx)
Proof
  simp[storage_trace_frame_def, get_address_immutables_def] >>
  rpt gen_tac >> Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  simp[lift_option_type_def, return_def, raise_def]
QED

Theorem storage_trace_frame_get_immutables:
  storage_trace_frame (get_immutables cx src)
Proof
  pure_rewrite_tac[get_immutables_def] >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_get_address_immutables, storage_trace_frame_return]
QED

Theorem storage_trace_frame_set_immutable:
  storage_trace_frame (set_immutable cx src nm ty v)
Proof
  pure_rewrite_tac[set_immutable_def] >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_get_address_immutables, storage_trace_frame_state_updates]
QED

Theorem storage_trace_frame_new_variable:
  storage_trace_frame (new_variable nm ty v)
Proof
  pure_rewrite_tac[new_variable_def] >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_state_reads] >> gen_tac >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_checks] >>
  Cases_on `v'` >>
  simp[storage_trace_frame_raise, storage_trace_frame_state_updates]
QED

Theorem storage_trace_frame_function_stack:
  storage_trace_frame (push_function fn sc cx) /\
  storage_trace_frame (pop_function scs)
Proof
  simp[storage_trace_frame_def, push_function_def, pop_function_def,
       set_scopes_def, return_def]
QED

Theorem storage_trace_frame_gas:
  storage_trace_frame next_gas_reading
Proof
  simp[storage_trace_frame_def, next_gas_reading_def, return_def, raise_def] >>
  gen_tac >> Cases_on `st.gas_obs` >> simp[]
QED

Theorem storage_trace_frame_transfer_value:
  storage_trace_frame (transfer_value sender target amount)
Proof
  pure_rewrite_tac[transfer_value_def] >>
  Cases_on `amount = 0 \/ sender = target`
  >- simp[storage_trace_frame_return] >> simp[] >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_state_reads] >> gen_tac >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_checks, storage_trace_frame_state_updates]
QED

Theorem send_call_value_storage_trace_frame:
  storage_trace_frame (send_call_value mut cx)
Proof
  simp[send_call_value_def] >> IF_CASES_TAC >>
  simp[storage_trace_frame_return] >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_checks, storage_trace_frame_transfer_value]
QED

Theorem storage_trace_frame_acquire_lock:
  storage_trace_frame (acquire_nonreentrant_lock addr slot view)
Proof
  pure_rewrite_tac[acquire_nonreentrant_lock_def] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_event] >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
  gen_tac >> irule storage_trace_frame_cond >>
  simp[storage_trace_frame_raise] >> irule storage_trace_frame_cond >>
  simp[storage_trace_frame_return, storage_trace_frame_state_updates]
QED

Theorem storage_trace_frame_release_lock:
  storage_trace_frame (release_nonreentrant_lock addr slot)
Proof
  pure_rewrite_tac[release_nonreentrant_lock_def] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_event] >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_state_reads, storage_trace_frame_state_updates]
QED

Theorem storage_trace_frame_read_place:
  storage_trace_frame (read_place cx place)
Proof
  Cases_on `place` >> pure_rewrite_tac[read_place_def]
  >- simp[storage_trace_frame_read_storage_slot]
  >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_state_reads, storage_trace_frame_get_immutables] >>
  gen_tac >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_lifts]
QED

Theorem storage_trace_frame_place_type:
  storage_trace_frame (place_type_value cx place)
Proof
  Cases_on `place` >> pure_rewrite_tac[place_type_value_def]
  >- simp[storage_trace_frame_return]
  >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_state_reads, storage_trace_frame_get_immutables] >>
  gen_tac >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_lifts]
QED

Theorem storage_trace_frame_read_result:
  storage_trace_frame (read_result cx result)
Proof
  Cases_on `result` >>
  simp[read_result_def, storage_trace_frame_return,
       storage_trace_frame_raise, storage_trace_frame_read_place]
QED

Theorem storage_trace_frame_read_results:
  storage_trace_frame (read_results cx results)
Proof
  Induct_on `results`
  >- simp[read_results_def, storage_trace_frame_return] >>
  gen_tac >> pure_rewrite_tac[read_results_def] >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_read_result] >> gen_tac >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_return]
QED

Theorem storage_trace_frame_conditional_result:
  storage_trace_frame (conditional_result cx result)
Proof
  Cases_on `result` >> pure_rewrite_tac[conditional_result_def]
  >- simp[storage_trace_frame_return]
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_place_type] >> gen_tac >>
      irule storage_trace_frame_cond >> simp[storage_trace_frame_return] >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_place, storage_trace_frame_return]) >>
  simp[storage_trace_frame_raise]
QED

Theorem storage_trace_frame_switch:
  storage_trace_frame f /\ storage_trace_frame g ==>
  storage_trace_frame (switch_BoolV cx result f g)
Proof
  strip_tac >> pure_rewrite_tac[switch_BoolV_def] >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_read_result] >>
  gen_tac >> irule storage_trace_frame_cond >> simp[] >>
  irule storage_trace_frame_cond >> simp[storage_trace_frame_raise]
QED

Theorem storage_trace_frame_loop_handler:
  storage_trace_frame (handle_loop_exception e)
Proof
  pure_rewrite_tac[handle_loop_exception_def] >>
  irule storage_trace_frame_cond >> simp[storage_trace_frame_return] >>
  irule storage_trace_frame_cond >>
  simp[storage_trace_frame_return, storage_trace_frame_raise]
QED

Theorem storage_trace_frame_function_handler:
  storage_trace_frame (handle_function e)
Proof
  Cases_on `e` >>
  simp[handle_function_def, storage_trace_frame_return, storage_trace_frame_raise]
QED

Theorem storage_trace_frame_get_place:
  storage_trace_frame (get_place result)
Proof
  Cases_on `result` >>
  simp[get_place_def, storage_trace_frame_return, storage_trace_frame_raise]
QED

Theorem storage_trace_frame_write_place:
  storage_trace_frame (write_place cx place v)
Proof
  Cases_on `place` >> pure_rewrite_tac[write_place_def]
  >- simp[storage_trace_frame_write_storage_slot]
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_state_reads] >> gen_tac >>
      irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      qx_gen_tac `parts` >> PairCases_on `parts` >> simp[] >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts, storage_trace_frame_state_updates]) >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_get_immutables] >> gen_tac >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
  gen_tac >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_lifts, storage_trace_frame_set_immutable]
QED

Theorem storage_trace_frame_lookup_flag:
  storage_trace_frame (lookup_flag_mem cx nsid mid)
Proof
  Cases_on `nsid` >> pure_rewrite_tac[lookup_flag_mem_def] >>
  Cases_on `get_module_code cx q`
  >- simp[storage_trace_frame_raise] >>
  Cases_on `lookup_flag r x`
  >- simp[storage_trace_frame_raise] >>
  Cases_on `INDEX_OF mid x'` >>
  simp[storage_trace_frame_return, storage_trace_frame_raise]
QED

Theorem storage_trace_frame_set_variable:
  storage_trace_frame (set_variable nm v)
Proof
  pure_rewrite_tac[set_variable_def] >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
  gen_tac >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_lifts] >>
  qx_gen_tac `parts` >> PairCases_on `parts` >> simp[] >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_checks, storage_trace_frame_state_updates]
QED

Theorem storage_trace_frame_lookup_global:
  storage_trace_frame (lookup_global cx src nm)
Proof
  pure_rewrite_tac[lookup_global_def] >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
  qx_gen_tac `ts` >> simp[] >>
  Cases_on `find_var_decl_by_name nm ts`
  >- (simp[] >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_get_immutables] >> qx_gen_tac `imms` >>
      Cases_on `FLOOKUP imms nm` >>
      simp[storage_trace_frame_return, storage_trace_frame_raise]) >>
  rename1 `find_var_decl_by_name nm ts = SOME info` >>
  PairCases_on `info` >> Cases_on `info0` >> simp[] >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts]
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts] >> gen_tac >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_event, storage_trace_frame_return]) >>
  simp[storage_trace_frame_return]
QED

Theorem storage_trace_frame_set_global:
  storage_trace_frame (set_global cx src nm v)
Proof
  pure_rewrite_tac[set_global_def] >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
  qx_gen_tac `ts` >> simp[] >>
  Cases_on `find_var_decl_by_name nm ts`
  >- simp[storage_trace_frame_raise] >>
  rename1 `find_var_decl_by_name nm ts = SOME info` >>
  PairCases_on `info` >> Cases_on `info0` >> simp[]
  >- (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts] >> gen_tac >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_event, storage_trace_frame_write_storage_slot]) >>
  simp[storage_trace_frame_raise]
QED

Theorem storage_trace_frame_resolve_array:
  !cx tr slot ty subs.
  storage_trace_frame (resolve_array_element cx tr slot ty subs)
Proof
  recInduct resolve_array_element_ind >> rpt strip_tac >>
  pure_rewrite_tac[resolve_array_element_def]
  >- (irule storage_trace_frame_bind_all >> conj_tac
      >- (simp[] >> metis_tac[]) >>
      (Cases_on `bd` >> simp[] >>
          irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks]
          >- simp[storage_trace_frame_return] >>
          irule storage_trace_frame_bind_all >>
          simp[storage_trace_frame_get_storage_backend] >> gen_tac >>
          irule storage_trace_frame_ignore_bind >>
          simp[storage_trace_frame_checks, storage_trace_frame_return]) >>
      simp[]) >>
  simp[storage_trace_frame_raise, storage_trace_frame_return]
QED

Theorem storage_trace_frame_extend_storage:
  !cx tr slot ty sb. storage_trace_frame (extend_storage_place cx tr slot ty sb)
Proof
  recInduct extend_storage_place_ind >> rpt strip_tac >>
  pure_rewrite_tac[extend_storage_place_def]
  >- (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      qx_gen_tac `parts` >> PairCases_on `parts` >>
      simp[storage_trace_frame_return])
  >- (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_resolve_array] >>
      qx_gen_tac `parts` >> PairCases_on `parts` >>
      simp[storage_trace_frame_return])
  >- (irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts, storage_trace_frame_return]) >>
  simp[storage_trace_frame_raise]
QED

Theorem storage_trace_frame_extend_place:
  !cx result sb. storage_trace_frame (extend_place cx result sb)
Proof
  recInduct extend_place_ind >> rpt strip_tac >>
  pure_rewrite_tac[extend_place_def]
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_extend_storage, storage_trace_frame_return])
  >- (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_place_type] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_read_place] >>
      gen_tac >> irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_lifts, storage_trace_frame_return])
  >- (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_place_type] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_read_place] >>
      gen_tac >> irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_lifts, storage_trace_frame_return])
  >- (simp[] >> Cases_on `vt` >> simp[storage_trace_frame_return] >>
      irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_event, storage_trace_frame_return]) >>
  simp[storage_trace_frame_raise]
QED

Theorem storage_trace_frame_select:
  !cx ty result sb. storage_trace_frame (select_result cx ty result sb)
Proof
  recInduct select_result_ind >> rpt strip_tac >>
  pure_rewrite_tac[select_result_def]
  >- (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts, storage_trace_frame_return]) >>
  simp[storage_trace_frame_extend_place]
QED

Theorem storage_trace_frame_array_length:
  !cx result. storage_trace_frame (result_array_length cx result)
Proof
  recInduct result_array_length_ind >> rpt strip_tac >>
  pure_rewrite_tac[result_array_length_def]
  >- simp[storage_trace_frame_return]
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_get_storage_backend, storage_trace_frame_return]) >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_read_result] >>
  qx_gen_tac `v` >> Cases_on `v` >>
  simp[storage_trace_frame_return, storage_trace_frame_raise] >>
  BasicProvers.PURE_CASE_TAC >>
  simp[storage_trace_frame_return, storage_trace_frame_raise]
QED

Theorem storage_trace_frame_append_place:
  !cx place v. storage_trace_frame (append_place cx place v)
Proof
  recInduct append_place_ind >> rpt strip_tac >>
  pure_rewrite_tac[append_place_def]
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_get_storage_backend] >> gen_tac >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_write_storage_slot]) >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_place_type] >>
  gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_read_place] >>
  gen_tac >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_lifts, storage_trace_frame_write_place]
QED

Theorem storage_trace_frame_pop_place:
  !cx place. storage_trace_frame (pop_place cx place)
Proof
  recInduct pop_place_ind >> rpt strip_tac >>
  pure_rewrite_tac[pop_place_def]
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_get_storage_backend] >> gen_tac >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_write_storage_slot, storage_trace_frame_return])
  >- (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      qx_gen_tac `parts` >> PairCases_on `parts` >> simp[] >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
      irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
      irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      qx_gen_tac `updated` >> PairCases_on `updated` >> simp[] >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates, storage_trace_frame_return])
  >- (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_get_immutables] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_set_immutable, storage_trace_frame_return]) >>
  simp[storage_trace_frame_raise]
QED

Theorem storage_trace_frame_optional_locks:
  storage_trace_frame (lock_if_nr cx nr view) /\
  storage_trace_frame (unlock_if_nr cx nr view)
Proof
  Cases_on `nr` >> Cases_on `view` >> Cases_on `cx.nonreentrant_slot` >>
  simp[lock_if_nr_def, unlock_if_nr_def, storage_trace_frame_return,
       storage_trace_frame_raise, storage_trace_frame_acquire_lock,
       storage_trace_frame_release_lock]
QED

Theorem storage_trace_frame_take_call:
  storage_trace_frame (take_call_outcome target calldata value_opt)
Proof
  pure_rewrite_tac[storage_trace_frame_def] >> rpt gen_tac >>
  Cases_on `st.outcomes` >>
  simp[take_call_outcome_def, call_outcome_request_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem storage_trace_frame_take_create:
  storage_trace_frame (take_create_outcome kind value initcode)
Proof
  pure_rewrite_tac[storage_trace_frame_def] >> rpt gen_tac >>
  Cases_on `st.outcomes` >>
  simp[take_create_outcome_def, create_outcome_request_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem storage_trace_frame_adopt:
  storage_trace_frame (adopt_call_outcome rq outcome)
Proof
  Cases_on `rq.cr_static` >> Cases_on `outcome.co_success` >>
  Cases_on `rq.cr_kind = MessageCall` >>
  simp[storage_trace_frame_def, adopt_call_outcome_equation]
QED

Theorem storage_trace_frame_create_oracle:
  storage_trace_frame (create_oracle_result salt value initcode rof)
Proof
  pure_rewrite_tac[storage_trace_frame_action] >> rpt gen_tac >>
  Cases_on `take_create_outcome
    (case salt of NONE => CreateCall | SOME s => Create2Call s) value initcode st` >>
  rename1 `take_create_outcome _ _ _ st = (result,mid)` >>
  `storage_trace_frame (take_create_outcome
    (case salt of NONE => CreateCall | SOME s => Create2Call s) value initcode)`
    by simp[storage_trace_frame_take_create] >>
  drule_all storage_trace_frame_result >>
  disch_then (qspec_then `p` assume_tac) >>
  Cases_on `result`
  >- (rename1 `INL pair` >> PairCases_on `pair` >>
      Cases_on `adopt_call_outcome pair0 pair1 mid` >>
      `storage_trace_frame (adopt_call_outcome pair0 pair1)`
        by simp[storage_trace_frame_adopt] >>
      drule_all storage_trace_frame_result >>
      disch_then (qspec_then `p` assume_tac) >>
      simp[create_oracle_result_def] >>
      rpt (IF_CASES_TAC >> simp[])) >>
  simp[create_oracle_result_def]
QED

Theorem storage_trace_frame_outcomes_read:
  storage_trace_frame (\st. return st.outcomes st) /\
  storage_trace_frame (\st. return (IS_SOME st.outcomes) st)
Proof
  simp[storage_trace_frame_def, return_def]
QED

Theorem storage_trace_frame_raw_call:
  storage_trace_frame (eval_raw_call cx flags target calldata amount gas)
Proof
  pure_rewrite_tac[eval_raw_call_def] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_outcomes_read] >>
  gen_tac >> irule storage_trace_frame_bind_all >> conj_tac
  >- (qx_gen_tac `result` >> PairCases_on `result` >> simp[] >>
      irule storage_trace_frame_cond >> conj_tac
      >- (irule storage_trace_frame_ignore_bind >> conj_tac
          >- (irule storage_trace_frame_cond >>
              simp[storage_trace_frame_return, storage_trace_frame_raise]) >>
          irule storage_trace_frame_cond >>
          simp[storage_trace_frame_return, storage_trace_frame_raise]) >>
      irule storage_trace_frame_cond >> simp[storage_trace_frame_return]) >>
  irule storage_trace_frame_cond >> conj_tac
  >- (irule storage_trace_frame_bind_all >> conj_tac
      >- (qx_gen_tac `result` >> PairCases_on `result` >> simp[] >>
          irule storage_trace_frame_ignore_bind >>
          simp[storage_trace_frame_adopt, storage_trace_frame_return]) >>
      simp[storage_trace_frame_take_call]) >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
  gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
  gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
  gen_tac >> simp[] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_state_updates] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_state_updates] >>
  irule storage_trace_frame_ignore_bind >> conj_tac
  >- (irule storage_trace_frame_cond >>
      simp[storage_trace_frame_backend, storage_trace_frame_return]) >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_state_updates, storage_trace_frame_return]
QED

Theorem storage_trace_frame_ext_effects:
  storage_trace_frame (eval_ext_call_effects cx target calldata value_opt gas accounts)
Proof
  pure_rewrite_tac[eval_ext_call_effects_def] >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_outcomes_read] >>
  qx_gen_tac `outcomes` >> Cases_on `outcomes` >> simp[]
  >- (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> simp[] >> irule storage_trace_frame_ignore_bind >> conj_tac
      >- (irule storage_trace_frame_cond >>
          simp[storage_trace_frame_return, storage_trace_frame_raise]) >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_state_updates] >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_state_updates] >>
      irule storage_trace_frame_ignore_bind >> conj_tac
      >- (irule storage_trace_frame_cond >>
          simp[storage_trace_frame_backend, storage_trace_frame_return]) >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates, storage_trace_frame_return]) >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_take_call] >>
  qx_gen_tac `result` >> PairCases_on `result` >> simp[] >>
  irule storage_trace_frame_ignore_bind >> conj_tac
  >- (irule storage_trace_frame_cond >>
      simp[storage_trace_frame_return, storage_trace_frame_raise]) >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_adopt, storage_trace_frame_return]
QED

Theorem storage_trace_frame_ext_call:
  storage_trace_frame (eval_ext_call cx static_flag skip_check sigt opts vs)
Proof
  PairCases_on `sigt` >> Cases_on `vs` >>
  simp[eval_ext_call_def, storage_trace_frame_raise] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
  gen_tac >> irule storage_trace_frame_bind_all >> conj_tac
  >- (gen_tac >> simp[] >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
      gen_tac >> irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
      irule storage_trace_frame_bind_all >> simp[storage_trace_frame_ext_effects] >>
      qx_gen_tac `returnData` >>
      Cases_on `if returnData = [] then ext_call_kwarg EKDefault opts (DROP (LENGTH sigt1) t) else NONE` >> simp[]
      >- (irule storage_trace_frame_bind_all >>
          simp[storage_trace_frame_lifts, storage_trace_frame_return]) >>
      irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
      gen_tac >> irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_checks, storage_trace_frame_return]) >>
  irule storage_trace_frame_cond >> simp[storage_trace_frame_return] >>
  BasicProvers.PURE_CASE_TAC >> simp[storage_trace_frame_return] >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_lifts, storage_trace_frame_return]
QED

Theorem storage_trace_frame_send:
  storage_trace_frame (eval_send cx has_gas vs)
Proof
  Cases_on `vs` >> simp[eval_send_def, storage_trace_frame_raise] >>
  Cases_on `t` >> simp[eval_send_def, storage_trace_frame_raise] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
  gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
  gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_outcomes_read] >>
  qx_gen_tac `outcomes` >> Cases_on `outcomes` >> simp[]
  >- (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
      gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
      gen_tac >> simp[] >> irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_state_updates] >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_state_updates] >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_backend] >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates, storage_trace_frame_return]) >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_take_call] >>
  qx_gen_tac `result` >> PairCases_on `result` >> simp[] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_adopt, storage_trace_frame_return]
QED

Theorem storage_trace_frame_check_create_blueprint:
  !has_salt vs. storage_trace_frame (check_create_blueprint has_salt vs)
Proof
  rpt gen_tac >> pure_rewrite_tac[check_create_blueprint_def] >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_state_reads, storage_trace_frame_lifts]
QED

Theorem storage_trace_frame_create_soft_failure:
  storage_trace_frame (create_soft_failure rof msg)
Proof
  simp[create_soft_failure_def, storage_trace_frame_cond,
       storage_trace_frame_raise, storage_trace_frame_return]
QED

Theorem storage_trace_frame_create:
  storage_trace_frame (eval_create cx kind has_salt rof arg_tys vs blueprint_size)
Proof
  pure_rewrite_tac[eval_create_def] >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
  gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
  gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
  gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >>
  gen_tac >> irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_bind_all >>
  simp[GSYM return_def, storage_trace_frame_outcomes_read] >>
  gen_tac >> irule storage_trace_frame_cond >>
  simp[storage_trace_frame_create_oracle] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_cond >> simp[storage_trace_frame_create_soft_failure] >>
  irule storage_trace_frame_cond >> conj_tac
  >- (irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates, storage_trace_frame_create_soft_failure]) >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
  irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
  gen_tac >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_state_reads] >>
  gen_tac >> irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_state_updates] >>
  qmatch_goalsub_abbrev_tac `run_create_evm a b c d e f g h` >>
  namedCases_on `run_create_evm a b c d e f g h` ["", "result"] >> simp[]
  >- (irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates, storage_trace_frame_create_soft_failure]) >>
  PairCases_on `result` >> simp[] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_state_updates] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_state_updates] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_backend] >>
  irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_state_updates] >>
  Cases_on `result0` >> simp[]
  >- (irule storage_trace_frame_cond >>
      simp[storage_trace_frame_raise, storage_trace_frame_return]) >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_state_updates, storage_trace_frame_return]
QED

Theorem storage_trace_frame_prefix:
  storage_trace_frame f /\ f st = (res,st') ==>
  ?observations. st'.storage_trace = st.storage_trace ++ observations
Proof
  pure_rewrite_tac[storage_trace_frame_def] >> strip_tac >>
  first_x_assum (qspecl_then [`st`, `st.storage_trace`] mp_tac) >>
  Cases_on `f (st with storage_trace := [])` >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem storage_trace_frame_erasure:
  storage_trace_frame f ==>
  FST (f st) = FST (f (erase_storage_trace st)) /\
  erase_storage_trace (SND (f st)) =
    erase_storage_trace (SND (f (erase_storage_trace st)))
Proof
  pure_rewrite_tac[storage_trace_frame_def] >> strip_tac >>
  first_x_assum (qspecl_then [`st`, `st.storage_trace`] mp_tac) >>
  Cases_on `f (st with storage_trace := [])` >>
  simp[erase_storage_trace_def] >> strip_tac >> simp[]
QED

Theorem storage_trace_frame_precompile_call_success:
  storage_trace_frame (precompile_call_success bt)
Proof
  rw[storage_trace_frame_def, precompile_call_success_def] >>
  rpt BasicProvers.TOP_CASE_TAC >> gvs[return_def, check_def, assert_def, raise_def, AllCaseEqs()]
QED

(* Deterministic composition at the frame boundary; recursive guards remain
   assumptions until all preceding successful computations are in context. *)
val trace_frame_atoms = List.concat (map (CONJUNCTS o SPEC_ALL)
  [storage_trace_frame_return, storage_trace_frame_raise,
   storage_trace_frame_checks, storage_trace_frame_lifts,
   storage_trace_frame_state_reads, storage_trace_frame_state_updates,
   storage_trace_frame_pop_scope, storage_trace_frame_function_stack,
   storage_trace_frame_read_results, storage_trace_frame_optional_locks,
   storage_trace_frame_function_handler, storage_trace_frame_loop_handler,
   storage_trace_frame_event, storage_trace_frame_backend,
   storage_trace_frame_gas, storage_trace_frame_transfer_value,
   storage_trace_frame_read_result, storage_trace_frame_read_place,
   storage_trace_frame_place_type, storage_trace_frame_get_place,
   storage_trace_frame_write_place, storage_trace_frame_lookup_flag,
   storage_trace_frame_set_variable, storage_trace_frame_lookup_global,
   storage_trace_frame_set_global, storage_trace_frame_new_variable,
   storage_trace_frame_extend_place, storage_trace_frame_select,
   storage_trace_frame_array_length, storage_trace_frame_append_place,
   storage_trace_frame_pop_place, storage_trace_frame_raw_call,
   storage_trace_frame_ext_call, storage_trace_frame_send,
   storage_trace_frame_create, storage_trace_frame_conditional_result,
   storage_trace_frame_check_create_blueprint,
   storage_trace_frame_precompile_call_success]);

val TRACE_FRAME_STEP = FIRST [
  CONV_TAC (HO_REWR_CONV pairTheory.FORALL_PROD), gen_tac,
  first_assum ACCEPT_TAC,
  FIRST (map MATCH_ACCEPT_TAC trace_frame_atoms),
  MATCH_MP_TAC storage_trace_frame_bind >> conj_tac,
  MATCH_MP_TAC storage_trace_frame_finally >> conj_tac,
  MATCH_MP_TAC storage_trace_frame_try >> conj_tac,
  MATCH_MP_TAC storage_trace_frame_switch >> conj_tac,
  CONV_TAC (RAND_CONV (REWR_CONV ignore_bind_def)),
  CHANGED_TAC (simp_tac bool_ss [LET_THM]),
  strip_tac, conj_tac,
  BasicProvers.TOP_CASE_TAC];

val TRACE_FRAME_GUARD_TAC = first_x_assum irule >>
  rpt (first_assum (irule_at Any)) >> simp[ignore_bind_def];

fun TRACE_FRAME_CONSTRUCTOR_TAC g = (rpt strip_tac >>
  pure_rewrite_tac[Once evaluate_def] >> rpt TRACE_FRAME_STEP >>
  TRACE_FRAME_GUARD_TAC) g;

Theorem evaluate_storage_trace_frame:
  (!cx s. storage_trace_frame (eval_stmt cx s)) /\
  (!cx ss. storage_trace_frame (eval_stmts cx ss)) /\
  (!cx it. storage_trace_frame (eval_iterator cx it)) /\
  (!cx tyv nm body vs. storage_trace_frame (eval_for cx tyv nm body vs)) /\
  (!cx e. storage_trace_frame (eval_expr cx e)) /\
  (!cx es. storage_trace_frame (eval_exprs cx es)) /\
  (!cx t. storage_trace_frame (eval_base_place cx t)) /\
  (!cx t. storage_trace_frame (eval_target_place cx t)) /\
  (!cx t v. storage_trace_frame (assign_tuple_targets cx t v)) /\
  (!cx ts vs. storage_trace_frame (assign_tuple_target_list cx ts vs)) /\
  (!cx es. storage_trace_frame (eval_expr_results cx es))
Proof
  ho_match_mp_tac evaluate_ind >>
  map_every (fn n => conj_tac >- suspend ("c" ^ Int.toString n))
    (List.tabulate (62, fn n => n + 1)) >> suspend "c63"
QED

Resume evaluate_storage_trace_frame[c24]:
  rpt strip_tac >> pure_rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  irule storage_trace_frame_bind >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED

Resume evaluate_storage_trace_frame[c42]:
  rpt strip_tac >> pure_rewrite_tac[Once evaluate_def] >>
  rpt TRACE_FRAME_STEP >> TRACE_FRAME_GUARD_TAC
QED

Resume evaluate_storage_trace_frame[c1]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c2]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c3]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c4]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c5]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c6]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c7]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c8]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c9]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c10]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c11]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c12]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c13]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c14]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c15]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c16]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c17]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c18]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c19]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c20]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c21]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c22]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c23]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c25]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c26]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c27]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c28]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c29]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c30]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c31]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c32]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c33]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c34]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c35]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c36]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c37]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c38]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c39]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c40]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c41]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c43]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c44]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c45]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c46]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c47]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c48]:
  rpt strip_tac >> pure_rewrite_tac[Once evaluate_def] >> rpt TRACE_FRAME_STEP >>
  gvs[] >> rpt TRACE_FRAME_STEP >> TRACE_FRAME_GUARD_TAC
QED
Resume evaluate_storage_trace_frame[c49]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c50]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c51]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c52]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c53]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c54]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c55]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c56]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c57]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c58]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c59]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c60]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c61]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c62]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED
Resume evaluate_storage_trace_frame[c63]:
  TRACE_FRAME_CONSTRUCTOR_TAC
QED

Finalise evaluate_storage_trace_frame


Theorem storage_trace_frame_eval_external_defaults:
  storage_trace_frame (eval_external_defaults cx es)
Proof
  pure_rewrite_tac[eval_external_defaults_def] >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_state_reads] >> gen_tac >>
  irule storage_trace_frame_finally >> conj_tac
  >- (irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates, evaluate_storage_trace_frame]) >>
  simp[storage_trace_frame_state_updates]
QED

Theorem storage_trace_frame_external_entry:
  storage_trace_frame
    (do send_call_value mut cx;
        dvs <- eval_external_defaults cx es;
        case bind_arguments tenv args (vals ++ dvs) of
          NONE => raise (Error (RuntimeError "call bind_arguments"))
        | SOME env => do
            set_scopes [env]; lock_if_nr cx nr view; eval_stmts cx stmts
          od
     od)
Proof
  irule storage_trace_frame_ignore_bind >>
  simp_tac bool_ss [send_call_value_storage_trace_frame] >>
  irule storage_trace_frame_bind_all >>
  simp_tac bool_ss [storage_trace_frame_eval_external_defaults] >> qx_gen_tac `dvs` >>
  Cases_on `bind_arguments tenv args (vals ++ dvs)` >>
  simp_tac bool_ss [optionTheory.option_CLAUSES, storage_trace_frame_raise] >>
  irule storage_trace_frame_ignore_bind >>
  simp_tac bool_ss [storage_trace_frame_state_updates] >>
  irule storage_trace_frame_ignore_bind >>
  simp_tac bool_ss [storage_trace_frame_optional_locks, evaluate_storage_trace_frame]
QED
