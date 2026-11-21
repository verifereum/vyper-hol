(* The source records an oracle request and its StorageOutcome together. *)
Theory s1PrefixRequestFrame
Ancestors
  e2eRequestCutDefs extCallOracle vyperState vyperCallOutcome
  vyperCallOutcomeProps vyperCallOutcomeFrame vyperMachineFrame vyperStatePreservation
  vyperInterpreter vyperCreate vyperPlaceFrames vyperStorageTrace list pair sum arithmetic
Libs monadsyntax evalWalkLib

val () = monadsyntax.enable_monad "vyper_evaluation";

Definition requests_outcomes_frame_def:
  requests_outcomes_frame f <=>
    state_rel_frame
      (\s t. LENGTH s.requests = recorded_outcomes_count s.storage_trace ==>
             LENGTH t.requests = recorded_outcomes_count t.storage_trace) f
End

Theorem requests_outcomes_frame_result:
  requests_outcomes_frame f /\ f st = (res,st') /\
  LENGTH st.requests = recorded_outcomes_count st.storage_trace ==>
  LENGTH st'.requests = recorded_outcomes_count st'.storage_trace
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_result] >> metis_tac[]
QED

Triviality request_count_appends[simp]:
  recorded_outcomes_count (obs ++ [StorageOutcome rq outcome]) =
    SUC (recorded_outcomes_count obs) /\
  recorded_outcomes_count (obs ++ [StorageRoot b slot ty]) =
    recorded_outcomes_count obs /\
  recorded_outcomes_count (obs ++ [StorageLock slot]) =
    recorded_outcomes_count obs /\
  recorded_outcomes_count (obs ++ [StorageBackend accounts transient]) =
    recorded_outcomes_count obs
Proof
  simp[recorded_outcomes_count_def, FILTER_APPEND_DISTRIB, ADD1]
QED

Theorem requests_outcomes_frame_bind:
  requests_outcomes_frame f /\
  (!v. (?s t. f s = (INL v,t)) ==> requests_outcomes_frame (g v)) ==>
  requests_outcomes_frame (bind f g)
Proof
  simp[requests_outcomes_frame_def] >> strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[] >> metis_tac[]
QED

Theorem requests_outcomes_frame_bind_all:
  requests_outcomes_frame f /\ (!v. requests_outcomes_frame (g v)) ==>
  requests_outcomes_frame (bind f g)
Proof
  simp[requests_outcomes_frame_bind]
QED

Triviality request_frame_try:
  requests_outcomes_frame f /\ (!e. requests_outcomes_frame (h e)) ==>
  requests_outcomes_frame (try f h)
Proof
  simp[requests_outcomes_frame_def] >> strip_tac >>
  irule state_rel_frame_try >> simp[]
QED

Triviality request_frame_finally:
  requests_outcomes_frame f /\ requests_outcomes_frame h ==>
  requests_outcomes_frame (finally f h)
Proof
  simp[requests_outcomes_frame_def] >> strip_tac >>
  irule state_rel_frame_finally >> simp[]
QED

Triviality request_frame_finally_unless_halt:
  requests_outcomes_frame f /\ requests_outcomes_frame h ==>
  requests_outcomes_frame (finally_unless_halt f h)
Proof
  simp[requests_outcomes_frame_def] >> strip_tac >>
  irule state_rel_frame_finally_unless_halt >> simp[]
QED

Triviality request_frame_choice:
  (b ==> requests_outcomes_frame f) /\ (~b ==> requests_outcomes_frame g) ==>
  requests_outcomes_frame (if b then f else g)
Proof
  Cases_on `b` >> simp[]
QED

Triviality request_frame_primitives:
  requests_outcomes_frame (return v) /\
  requests_outcomes_frame (\s. return (f s) s) /\
  requests_outcomes_frame (\s. (INL (IS_SOME s.outcomes),s)) /\
  requests_outcomes_frame (raise e) /\
  requests_outcomes_frame (type_check b msg) /\
  requests_outcomes_frame (check b msg) /\
  requests_outcomes_frame (check_not_static cx) /\
  requests_outcomes_frame (lift_option opt msg) /\
  requests_outcomes_frame (lift_option_type opt msg) /\
  requests_outcomes_frame (lift_sum sum) /\
  requests_outcomes_frame (lift_sum_runtime rs) /\
  requests_outcomes_frame get_accounts /\
  requests_outcomes_frame get_transient_storage /\
  requests_outcomes_frame get_pending_deletions /\
  requests_outcomes_frame get_scopes /\
  requests_outcomes_frame (update_accounts fa) /\
  requests_outcomes_frame (update_transient ft) /\
  requests_outcomes_frame (update_pending_deletions fp) /\
  requests_outcomes_frame (push_log lg) /\
  requests_outcomes_frame (append_logs ls) /\
  requests_outcomes_frame (set_scopes scs) /\
  requests_outcomes_frame push_scope /\
  requests_outcomes_frame (push_scope_with_var nm ty value) /\
  requests_outcomes_frame (set_address_immutables cx imms) /\
  requests_outcomes_frame pop_scope /\
  requests_outcomes_frame (push_function fn sc cx) /\
  requests_outcomes_frame (pop_function scs) /\
  requests_outcomes_frame next_gas_reading /\
  requests_outcomes_frame record_storage_backend /\
  requests_outcomes_frame (record_storage_event (StorageRoot b' slot ty)) /\
  requests_outcomes_frame (record_storage_event (StorageLock slot))
Proof
  rpt conj_tac >> simp[requests_outcomes_frame_def, state_rel_frame_def,
    return_def, raise_def, type_check_def, check_def, assert_def,
    check_not_static_def, lift_option_def, lift_option_type_def,
    lift_sum_def, lift_sum_runtime_def, get_accounts_def,
    get_transient_storage_def, get_pending_deletions_def, get_scopes_def,
    update_accounts_def, update_transient_def, update_pending_deletions_def,
    push_log_def, append_logs_def, set_scopes_def, push_scope_def,
    push_scope_with_var_def, set_address_immutables_def, pop_scope_def,
    push_function_def, pop_function_def, next_gas_reading_def,
    record_storage_backend_def, record_storage_event_def] >>
  rpt strip_tac >> rpt BasicProvers.TOP_CASE_TAC >> simp[return_def, raise_def]
QED

Triviality request_frame_take_request:
  requests_outcomes_frame (take_request_outcome rq)
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_def] >>
  qx_gen_tac `st` >> Cases_on `st.outcomes` >> simp[take_request_outcome_def] >>
  rename1 `st.outcomes = SOME os` >> Cases_on `os` >>
  simp[take_request_outcome_def] >> pairarg_tac >>
  simp[record_request_def] >> IF_CASES_TAC >> simp[]
QED

Triviality request_frame_take_create:
  requests_outcomes_frame (take_create_outcome kind amount code)
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_def] >>
  qx_gen_tac `st` >> Cases_on `st.outcomes` >> simp[take_create_outcome_def] >>
  rename1 `st.outcomes = SOME os` >> Cases_on `os` >>
  simp[take_create_outcome_def] >> pairarg_tac >>
  simp[record_request_def] >> IF_CASES_TAC >> simp[]
QED

Triviality request_frame_take:
  requests_outcomes_frame (take_call_outcome gas_cap target data value) /\
  requests_outcomes_frame (take_delegate_outcome gas_cap target data value)
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_def,
       take_call_outcome_def, take_delegate_outcome_def] >>
  metis_tac[REWRITE_RULE[requests_outcomes_frame_def, state_rel_frame_def]
    (GEN_ALL request_frame_take_request)]
QED

Triviality request_frame_adopt:
  requests_outcomes_frame (adopt_call_outcome rq outcome)
Proof
  Cases_on `rq.cr_static` >> Cases_on `outcome.co_success` >>
  Cases_on `rq.cr_kind = MessageCall` >> Cases_on `rq.cr_kind = DelegateMessageCall` >>
  simp[requests_outcomes_frame_def, state_rel_frame_def, adopt_call_outcome_equation]
QED

Triviality request_frame_state_unchanged:
  (!s res t. f s = (res,t) ==> t = s) ==> requests_outcomes_frame f
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_result] >> metis_tac[]
QED

Triviality request_frame_reads:
  requests_outcomes_frame (read_place cx p) /\
  requests_outcomes_frame (place_type_value cx p) /\
  requests_outcomes_frame (read_result cx result) /\
  requests_outcomes_frame (read_results cx results) /\
  requests_outcomes_frame (conditional_result cx result) /\
  requests_outcomes_frame (get_place result)
Proof
  rpt conj_tac >> irule request_frame_state_unchanged >>
  metis_tac[read_place_state, place_type_value_state, read_result_state,
            read_results_state, conditional_result_state, get_place_state]
QED

fun request_walk leaves unfolds =
  let
    val rules = [requests_outcomes_frame_bind, request_frame_try,
      request_frame_finally, request_frame_finally_unless_halt, request_frame_choice]
    val atoms = List.concat (map (CONJUNCTS o SPEC_ALL) leaves)
    val net = evalWalkLib.walk_net (map SPEC_ALL rules)
      (map (fn th => (concl th, MATCH_ACCEPT_TAC th)) atoms)
    val ih = evalWalkLib.IH_TAC {stop = K false,
      normalise = SIMP_RULE bool_ss
        [oneTheory.one, ignore_bind_def, FST, SND, pair_case_thm, UNCURRY,
         lock_if_nr_def, unlock_if_nr_def]}
  in
    evalWalkLib.STEP {net = net, at = RAND_CONV, unfolds = unfolds,
      intros = [CONV_TAC (HO_REWR_CONV FORALL_PROD), gen_tac, strip_tac, conj_tac,
        CONV_TAC (RAND_CONV ETA_CONV),
        CHANGED_TAC (fn (asl,w) => simp_tac bool_ss
          (pair_case_thm :: UNCURRY :: List.map ASSUME (List.filter is_eq asl)) (asl,w))],
      fallbacks = [ih, evalWalkLib.NORMALISE_IH_TAC ih]}
  end;

val request_primitive_frames =
  [request_frame_primitives, request_frame_reads, request_frame_take,
   request_frame_take_create, request_frame_adopt];

val request_common_unfolds =
  [ignore_bind_def, switch_BoolV_def, check_not_static_def,
   get_storage_backend_def, set_storage_backend_def, read_storage_slot_def,
   write_storage_slot_def, get_address_immutables_def, get_immutables_def,
   set_immutable_def, new_variable_def, transfer_value_def,
   send_call_value_def, frame_call_value_def, handle_loop_exception_def,
   handle_function_def, acquire_nonreentrant_lock_def,
   release_nonreentrant_lock_def, lock_if_nr_def, unlock_if_nr_def,
   create_soft_failure_def, check_create_blueprint_def];

val REQUEST_PRIMITIVE_STEP =
  request_walk request_primitive_frames request_common_unfolds;

Triviality request_frame_storage_backend:
  requests_outcomes_frame (get_storage_backend cx transient) /\
  requests_outcomes_frame (set_storage_backend cx transient backend)
Proof
  Cases_on `transient` >> simp[get_storage_backend_def, set_storage_backend_def] >>
  rpt REQUEST_PRIMITIVE_STEP
QED

Triviality request_frame_address_immutables:
  requests_outcomes_frame (get_address_immutables cx)
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_def,
       get_address_immutables_def, lift_option_type_def] >>
  qx_gen_tac `st` >> Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  simp[return_def, raise_def]
QED

val request_storage_frames =
  request_frame_storage_backend :: request_frame_address_immutables ::
  request_primitive_frames;

val REQUEST_STORAGE_STEP = request_walk request_storage_frames request_common_unfolds;

Triviality request_frame_resolve_array:
  requests_outcomes_frame (resolve_array_element cx tr slot ty subs)
Proof
  irule request_frame_state_unchanged >> metis_tac[resolve_array_element_state]
QED

Triviality request_frame_storage_and_locals:
  requests_outcomes_frame (write_place cx place v) /\
  requests_outcomes_frame (lookup_flag_mem cx nsid mid) /\
  requests_outcomes_frame (set_variable nm v) /\
  requests_outcomes_frame (lookup_global cx src nm) /\
  requests_outcomes_frame (set_global cx src nm v)
Proof
  rpt conj_tac >>
  PURE_REWRITE_TAC[write_place_def, lookup_flag_mem_def, set_variable_def,
                   lookup_global_def, set_global_def]
  >- (Cases_on `place` >> pure_rewrite_tac[write_place_def] >>
      rpt REQUEST_STORAGE_STEP)
  >- (PairCases_on `nsid` >> pure_rewrite_tac[lookup_flag_mem_def] >>
      rpt REQUEST_STORAGE_STEP) >>
  rpt REQUEST_STORAGE_STEP
QED

Triviality request_frame_extend_storage:
  !cx tr slot ty sb. requests_outcomes_frame (extend_storage_place cx tr slot ty sb)
Proof
  recInduct extend_storage_place_ind >> rpt strip_tac >>
  pure_rewrite_tac[extend_storage_place_def] >>
  rpt (request_walk (request_frame_resolve_array :: request_storage_frames)
    request_common_unfolds)
QED

Triviality request_frame_extend_place:
  !cx result sb. requests_outcomes_frame (extend_place cx result sb)
Proof
  recInduct extend_place_ind >> rpt strip_tac >>
  pure_rewrite_tac[extend_place_def] >>
  rpt (request_walk (request_frame_extend_storage :: request_storage_frames)
    request_common_unfolds)
QED

Triviality request_frame_select:
  !cx ty result sb. requests_outcomes_frame (select_result cx ty result sb)
Proof
  recInduct select_result_ind >> rpt strip_tac >>
  pure_rewrite_tac[select_result_def] >>
  rpt (request_walk (request_frame_extend_place :: request_storage_frames)
    request_common_unfolds)
QED

Triviality request_frame_array_length:
  !cx result. requests_outcomes_frame (result_array_length cx result)
Proof
  recInduct result_array_length_ind >> rpt strip_tac >>
  pure_rewrite_tac[result_array_length_def] >> rpt REQUEST_STORAGE_STEP
QED

val request_place_frames =
  [request_frame_storage_and_locals, request_frame_extend_place,
   request_frame_select, request_frame_array_length] @ request_storage_frames;

val REQUEST_PLACE_STEP = request_walk request_place_frames request_common_unfolds;

Triviality request_frame_append_place:
  !cx place v. requests_outcomes_frame (append_place cx place v)
Proof
  recInduct append_place_ind >> rpt strip_tac >>
  pure_rewrite_tac[append_place_def] >> rpt REQUEST_PLACE_STEP
QED

Triviality request_frame_pop_place:
  !cx place. requests_outcomes_frame (pop_place cx place)
Proof
  recInduct pop_place_ind >> rpt strip_tac >>
  pure_rewrite_tac[pop_place_def] >> rpt REQUEST_PLACE_STEP
QED

Triviality request_frame_raw_call:
  requests_outcomes_frame (eval_raw_call cx flags target calldata amount gas)
Proof
  pure_rewrite_tac[eval_raw_call_def] >> rpt REQUEST_PRIMITIVE_STEP
QED

Triviality request_frame_ext_call:
  requests_outcomes_frame (eval_ext_call cx static_flag skip_check sigt opts vs)
Proof
  PairCases_on `sigt` >> Cases_on `vs` >>
  simp[eval_ext_call_def] >>
  rpt (request_walk request_primitive_frames
    (eval_ext_call_effects_def :: request_common_unfolds))
QED

Triviality request_frame_send:
  requests_outcomes_frame (eval_send cx gas vs)
Proof
  Cases_on `vs` >> simp[eval_send_def]
  >- rpt REQUEST_PRIMITIVE_STEP >>
  Cases_on `t` >> simp[eval_send_def] >> rpt REQUEST_PRIMITIVE_STEP
QED

Triviality request_frame_create_oracle:
  requests_outcomes_frame (create_oracle_result salt value initcode rof)
Proof
  simp[requests_outcomes_frame_def, state_rel_frame_def] >>
  qx_gen_tac `st` >> strip_tac >>
  qabbrev_tac `kind = case salt of NONE => CreateCall | SOME s => Create2Call s` >>
  Cases_on `take_create_outcome kind value initcode st` >>
  rename1 `take_create_outcome kind value initcode st = (res,mid)` >>
  `LENGTH mid.requests = recorded_outcomes_count mid.storage_trace` by
    metis_tac[requests_outcomes_frame_result, request_frame_take_create] >>
  pure_rewrite_tac[create_oracle_result_def] >> qpat_assum `Abbrev (kind = _)`
    (fn th => simp [GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
  Cases_on `res` >> gvs[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `adopt_call_outcome x0 x1 mid` >>
  `LENGTH r.requests = recorded_outcomes_count r.storage_trace` by
    metis_tac[requests_outcomes_frame_result, request_frame_adopt] >>
  rw[]
QED

Triviality request_frame_create:
  requests_outcomes_frame (eval_create cx kind has_salt rof arg_tys vs blueprint_size)
Proof
  pure_rewrite_tac[eval_create_def] >>
  rpt (request_walk (request_frame_create_oracle :: request_primitive_frames)
    request_common_unfolds)
QED

Triviality request_frame_precompile:
  requests_outcomes_frame (precompile_call_success bt vs)
Proof
  rewrite_tac[requests_outcomes_frame_def, state_rel_frame_def] >>
  qx_gen_tac `st` >>
  Cases_on `precompile_builtin bt` >> simp[precompile_call_success_def, return_def] >>
  Cases_on `st.outcomes` >> simp[return_def] >>
  rename1 `st.outcomes = SOME os` >> Cases_on `os` >>
  simp[check_def, assert_def, bind_def, take_call_outcome_def,
       take_request_outcome_def, call_outcome_request_def] >>
  pairarg_tac >> simp[bind_def, check_def, assert_def, record_request_def, AllCaseEqs()] >>
  Cases_on `outcome.co_success` >> simp[]
QED

Triviality request_frame_handle_function:
  requests_outcomes_frame (handle_function ex)
Proof
  Cases_on `ex` >> simp[handle_function_def] >> rpt REQUEST_PRIMITIVE_STEP
QED

val REQUEST_EVAL_STEP =
  request_walk
    ([request_frame_precompile, request_frame_raw_call, request_frame_ext_call,
      request_frame_send, request_frame_create, request_frame_handle_function,
      request_frame_append_place, request_frame_pop_place] @ request_place_frames)
    ([conditional_result_def, array_iterator_results_def, eval_create_operands_def] @
     request_common_unfolds);

val REQUEST_EVAL_CASE = evalWalkLib.EVAL_CASE (rpt strip_tac) REQUEST_EVAL_STEP;

Theorem evaluate_requests_outcomes_frame:
  (!cx s. requests_outcomes_frame (eval_stmt cx s)) /\
  (!cx ss. requests_outcomes_frame (eval_stmts cx ss)) /\
  (!cx it. requests_outcomes_frame (eval_iterator cx it)) /\
  (!cx tyv nm body vs. requests_outcomes_frame (eval_for cx tyv nm body vs)) /\
  (!cx e. requests_outcomes_frame (eval_expr cx e)) /\
  (!cx es. requests_outcomes_frame (eval_exprs cx es)) /\
  (!cx t. requests_outcomes_frame (eval_base_place cx t)) /\
  (!cx t. requests_outcomes_frame (eval_target_place cx t)) /\
  (!cx t v. requests_outcomes_frame (assign_tuple_targets cx t v)) /\
  (!cx ts vs. requests_outcomes_frame (assign_tuple_target_list cx ts vs))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> REQUEST_EVAL_CASE
QED
