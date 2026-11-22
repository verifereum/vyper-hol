Theory vyperEvalReadingErrors
Ancestors
  list pair option vyperState vyperInterpreter vyperCreate vyperMisc
  vyperCallOutcome vyperCallOutcomeProps vyperCallOutcomeBranches
  vyperStatePreservation vyperPureReadingErrors vyperContext
Libs
  monadsyntax pairLib evalWalkLib

val missing_msg = ``"msg.gas: no gas reading"``;
val missing_exc = ``Error (RuntimeError ^missing_msg)``;

(* The invariant follows the exact exception, not all RuntimeErrors. *)
Theorem reading_bind[local]:
  (f st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (!v mid. f st = (INL v,mid) ==>
    g v mid = (INR ^missing_exc,st') ==> st'.gas_obs = []) ==>
  vyperState$bind f g st = (INR ^missing_exc,st') ==> st'.gas_obs = []
Proof
  rpt strip_tac >> Cases_on `f st` >> rename1 `f st = (res,mid)` >>
  Cases_on `res` >> gvs[bind_def] >> metis_tac[]
QED

Theorem reading_try[local]:
  (f st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (!e mid. h e mid = (INR ^missing_exc,st') ==>
            e = ^missing_exc /\ mid = st') ==>
  try f h st = (INR ^missing_exc,st') ==> st'.gas_obs = []
Proof
  simp[try_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem reading_finally[local]:
  (!mid. f st = (INR ^missing_exc,mid) ==> mid.gas_obs = []) /\
  (!mid. g mid = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (!mid v. g mid = (INL v,st') ==> st'.gas_obs = mid.gas_obs) ==>
  finally f g st = (INR ^missing_exc,st') ==> st'.gas_obs = []
Proof
  simp[finally_def, ignore_bind_apply, return_def, raise_def,
       AllCaseEqs()] >> metis_tac[]
QED

Theorem reading_finally_unless_halt[local]:
  (!mid. f st = (INR ^missing_exc,mid) ==> mid.gas_obs = []) /\
  (!mid. g mid = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (!mid v. g mid = (INL v,st') ==> st'.gas_obs = mid.gas_obs) ==>
  finally_unless_halt f g st = (INR ^missing_exc,st') ==> st'.gas_obs = []
Proof
  simp[finally_unless_halt_def, ignore_bind_apply, return_def, raise_def,
       AllCaseEqs()] >> metis_tac[]
QED

Theorem reading_handlers[local]:
  (handle_loop_exception e st = (INR ^missing_exc,st') ==>
    e = ^missing_exc /\ st = st') /\
  (handle_function e st = (INR ^missing_exc,st') ==>
    e = ^missing_exc /\ st = st')
Proof
  Cases_on `e` >> simp[handle_loop_exception_def, handle_function_def,
                        return_def, raise_def]
QED

Theorem reading_cleanup[local]:
  (pop_scope st = (INL v,st') ==> st'.gas_obs = st.gas_obs) /\
  (!v. set_scopes scs st = (INL v,st') ==> st'.gas_obs = st.gas_obs) /\
  (pop_function prev st = (INL v,st') ==> st'.gas_obs = st.gas_obs) /\
  (unlock_if_nr cx nr view st = (INL v,st') ==> st'.gas_obs = st.gas_obs)
Proof
  simp[pop_scope_def, pop_function_def, set_scopes_def, unlock_if_nr_def,
       release_nonreentrant_lock_def, ignore_bind_def, bind_def,
       get_transient_storage_def, update_transient_def, record_storage_event_def,
       return_def, raise_def, COND_RATOR, option_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem reading_next_gas[local]:
  next_gas_reading st = (INR ^missing_exc,st') ==> st'.gas_obs = []
Proof
  Cases_on `st.gas_obs` >> gvs[next_gas_reading_def, return_def, raise_def] >>
  strip_tac >> gvs[]
QED

Theorem reading_lifts[local]:
  (lift_sum x st = (INR ^missing_exc,st') <=> x = INR (RuntimeError ^missing_msg) /\ st = st') /\
  (lift_sum_runtime y st = (INR ^missing_exc,st') <=> y = INR ^missing_msg /\ st = st') /\
  (lift_option opt msg st = (INR ^missing_exc,st') <=> opt = NONE /\ msg = ^missing_msg /\ st = st') /\
  (lift_option_type opt msg st <> (INR ^missing_exc,st'))
Proof
  simp[lift_sum_def, lift_sum_runtime_def, lift_option_def, lift_option_type_def,
       return_def, raise_def, sum_CASE_rator, option_CASE_rator, AllCaseEqs()]
QED

(* Match the result implication without consuming it as a successful-prefix
   guard.  The induction hypotheses retain their actual execution guards. *)
fun is_reading_concl tm = can (match_term ``(s:evaluation_state).gas_obs = []``) tm;
fun is_reading_rule tm = is_imp tm andalso is_reading_concl (snd (dest_imp tm));
val READING_IH = evalWalkLib.IH_TAC {stop = is_reading_rule, normalise = I};

fun READING_INTRO (g as (_,w)) =
  (if is_forall w then gen_tac
   else if is_imp w andalso not (is_reading_concl (snd (dest_imp w))) then strip_tac
   else NO_TAC) g;

Theorem reading_self_lift[local]:
  !cx vs st st'.
    lift_sum (evaluate_self_codesize cx vs) st <> (INR ^missing_exc,st')
Proof
  Cases_on `vs` >> simp[vyperContextTheory.evaluate_self_codesize_def,
    lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `h` >> Cases_on `t` >>
  gvs[vyperContextTheory.evaluate_self_codesize_def,
      lift_sum_def, return_def, raise_def, AllCaseEqs()]
QED

val reading_primitives = [return_def, raise_def, reading_lifts,
    reading_self_lift, pure_reading_error_exclusions, type_check_def,
    check_def, assert_def];

(* Prefer a fact about the exposed computation to splits inside its data
   arguments (for example the array-bound case buried in a return value). *)
fun READING_WALK facts unfolds =
  let
    val rules = [reading_bind, reading_try, reading_finally, reading_finally_unless_halt];
    val leaves = List.concat (map (map SPEC_ALL o CONJUNCTS o SPEC_ALL)
                                 (reading_next_gas :: facts));
    val net = evalWalkLib.walk_net (map SPEC_ALL rules)
      (map (fn th => (concl th, MATCH_ACCEPT_TAC th)) leaves);
    val at = LAND_CONV o LHS_CONV;
    val unfold = evalWalkLib.unfold_conv (ignore_bind_def :: unfolds);
  in
    rpt (FIRST [first_assum MATCH_ACCEPT_TAC,
      (fn g as (_,w) => FIRST (Net.match w net) g),
      READING_IH, READING_INTRO, conj_tac,
      CONV_TAC (at unfold), CONV_TAC (at (CHANGED_CONV evalWalkLib.head_conv)),
      CHANGED_TAC (simp_tac (srw_ss()) reading_primitives),
      evalWalkLib.HEAD_CASE_TAC, evalWalkLib.NORMALISE_IH_TAC READING_IH])
  end;

(* Leaves that return directly, without another evaluator call. *)
Theorem reading_direct_primitives[local]:
  (record_storage_event obs st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (record_storage_backend st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (get_scopes st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (set_scopes scs st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (push_scope st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (pop_scope st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (push_scope_with_var nm tv v st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (new_variable nm tv v st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (get_accounts st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (update_accounts fa st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (get_transient_storage st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (update_transient ft st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (get_pending_deletions st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (update_pending_deletions fp st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (push_log lg st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (append_logs ls st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (get_address_immutables cx st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (set_address_immutables cx imm st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (push_function sig sc cx st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (pop_function scs st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (check_not_static cx st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (release_nonreentrant_lock a slot st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (unlock_if_nr cx nr view st = (INR ^missing_exc,st') ==> st'.gas_obs = [])
Proof
  simp[record_storage_event_def, record_storage_backend_def, get_scopes_def,
       set_scopes_def, push_scope_def, pop_scope_def, push_scope_with_var_def,
       new_variable_def, get_accounts_def, update_accounts_def,
       get_transient_storage_def, update_transient_def, get_pending_deletions_def,
       update_pending_deletions_def, push_log_def, append_logs_def,
       get_address_immutables_def, set_address_immutables_def, push_function_def,
       pop_function_def, unlock_if_nr_def, release_nonreentrant_lock_def,
       ignore_bind_def, bind_def, return_def, raise_def, UNCURRY, LET_THM,
       type_check_def, assert_def, reading_lifts,
       COND_RATOR, option_CASE_rator, list_CASE_rator, AllCaseEqs()]
QED

Theorem reading_storage_backend[local]:
  (get_storage_backend cx tr st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (set_storage_backend cx tr sb st = (INR ^missing_exc,st') ==> st'.gas_obs = [])
Proof
  Cases_on `tr` >>
  READING_WALK [reading_direct_primitives] [get_storage_backend_def, set_storage_backend_def]
QED

val reading_base = [reading_handlers, reading_cleanup, reading_direct_primitives,
                    reading_storage_backend];

Theorem reading_state_operations[local]:
  (read_storage_slot cx tr slot tv st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (write_storage_slot cx tr slot tv v st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (get_immutables cx src st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (set_immutable cx src nm tv v st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (lookup_global cx src nm st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (lookup_flag_mem cx nsid mid st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (acquire_nonreentrant_lock addr lock view st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (transfer_value addr dest amount st = (INR ^missing_exc,st') ==> st'.gas_obs = [])
Proof
  READING_WALK reading_base [read_storage_slot_def, write_storage_slot_def,
    get_immutables_def, set_immutable_def, lookup_global_def, oneline lookup_flag_mem_def,
    acquire_nonreentrant_lock_def, transfer_value_def]
QED

val reading_base = reading_state_operations :: reading_base;

Theorem reading_places[local]:
  (read_place cx p st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (place_type_value cx p st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (write_place cx p v st = (INR ^missing_exc,st') ==> st'.gas_obs = [])
Proof
  Cases_on `p` >>
  READING_WALK reading_base [read_place_def, place_type_value_def, write_place_def]
QED

val reading_base = reading_places :: reading_base;

Theorem reading_result[local]:
  (read_result cx pv st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (conditional_result cx pv st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (get_place pv st = (INR ^missing_exc,st') ==> st'.gas_obs = [])
Proof
  Cases_on `pv` >>
  READING_WALK reading_base [read_result_def, conditional_result_def, get_place_def]
QED

val reading_base = reading_result :: reading_base;

Theorem reading_results[local]:
  !results cx st st'.
    read_results cx results st = (INR ^missing_exc,st') ==> st'.gas_obs = []
Proof
  Induct >> simp_tac bool_ss [Once read_results_def] >> READING_WALK reading_base []
QED

Theorem reading_array_length[local]:
  !cx pv st st'.
    result_array_length cx pv st = (INR ^missing_exc,st') ==> st'.gas_obs = []
Proof
  ho_match_mp_tac result_array_length_ind >>
  rpt conj_tac >> rpt READING_INTRO >> simp_tac bool_ss [Once result_array_length_def] >>
  READING_WALK reading_base []
QED

Theorem reading_resolve_array[local]:
  !cx tr slot tv path st st'.
    resolve_array_element cx tr slot tv path st = (INR ^missing_exc,st') ==> st'.gas_obs = []
Proof
  ho_match_mp_tac resolve_array_element_ind >>
  rpt conj_tac >> rpt READING_INTRO >> simp_tac bool_ss [Once resolve_array_element_def] >>
  READING_WALK reading_base []
QED

val reading_base = reading_results :: reading_array_length :: reading_resolve_array :: reading_base;

Theorem reading_extend_storage_place[local]:
  extend_storage_place cx tr slot tv sb st = (INR ^missing_exc,st') ==> st'.gas_obs = []
Proof
  READING_WALK reading_base [oneline extend_storage_place_def]
QED

Theorem reading_extend_place[local]:
  extend_place cx pv sb st = (INR ^missing_exc,st') ==> st'.gas_obs = []
Proof
  READING_WALK (reading_extend_storage_place :: reading_base) [oneline extend_place_def]
QED

val reading_base = reading_extend_place :: reading_base;

Theorem reading_place_operations[local]:
  (select_result cx ty pv sb st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (array_iterator_results cx ty pv st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (append_place cx p v st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (pop_place cx p st = (INR ^missing_exc,st') ==> st'.gas_obs = [])
Proof
  conj_tac >- READING_WALK reading_base [oneline select_result_def] >>
  conj_tac >- (Cases_on `?tr slot etv bd. pv = PlaceR (StoragePlace tr slot (ArrayTV etv bd))`
    >- (gvs[array_iterator_results_storage] >> READING_WALK reading_base []) >>
    `!tr slot etv bd. pv <> PlaceR (StoragePlace tr slot (ArrayTV etv bd))` by metis_tac[] >>
    drule array_iterator_results_copy >> disch_then (fn th => rewrite_tac[th]) >>
    READING_WALK reading_base []) >>
  conj_tac >- READING_WALK reading_base [oneline append_place_def] >>
  READING_WALK reading_base [oneline pop_place_def] >>
  rpt strip_tac >> gvs[pure_reading_error_exclusions]
QED

val reading_base = reading_place_operations :: reading_base;

Theorem reading_call_primitives[local]:
  (frame_call_value cx vo st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (precompile_call_success bt vs st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (take_call_outcome gas_cap addr data vo st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (take_delegate_outcome gas_cap addr data vo st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (adopt_call_outcome rq co st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (create_oracle_result salt value code rof st = (INR ^missing_exc,st') ==> st'.gas_obs = [])
Proof
  conj_tac >- READING_WALK reading_base [frame_call_value_def] >>
  conj_tac >-
    (Cases_on `st.outcomes` >>
     simp[precompile_call_success_def, return_def, COND_RATOR] >>
     rename1 `st.outcomes = SOME os` >> Cases_on `os` >>
     simp[check_def, assert_def, bind_def, AllCaseEqs()] >>
     Cases_on `take_call_outcome NONE (precompile_address bt)
       (precompile_input bt vs) NONE st` >>
     rename1 `take_call_outcome _ _ _ _ _ = (res,mid)` >>
     Cases_on `res` >> simp[UNCURRY, check_def, assert_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >> drule take_call_outcome_error >> simp[]) >>
  conj_tac >- (strip_tac >> drule take_call_outcome_error >> simp[]) >>
  conj_tac >- (strip_tac >> drule take_delegate_outcome_error >> simp[]) >>
  conj_tac >- simp[adopt_call_outcome_equation] >>
  simp[create_oracle_result_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> drule take_create_outcome_error >> simp[]
QED

val reading_base = reading_call_primitives :: reading_base;

Theorem reading_raw_call[local]:
  eval_raw_call cx flags addr data amount gas st = (INR ^missing_exc,st') ==>
  st'.gas_obs = []
Proof
  READING_WALK reading_base [eval_raw_call_def]
QED

Theorem reading_ext_call_effects[local]:
  eval_ext_call_effects cx addr data vo gas accounts st = (INR ^missing_exc,st') ==>
  st'.gas_obs = []
Proof
  READING_WALK reading_base [eval_ext_call_effects_def]
QED

Theorem reading_ext_call[local]:
  eval_ext_call cx static skip sig opts vs st = (INR ^missing_exc,st') ==>
  st'.gas_obs = []
Proof
  PairCases_on `sig` >> Cases_on `vs` >>
  READING_WALK (reading_ext_call_effects :: reading_base) [eval_ext_call_def]
QED

Theorem reading_send[local]:
  eval_send cx has_gas vs st = (INR ^missing_exc,st') ==> st'.gas_obs = []
Proof
  READING_WALK reading_base [oneline eval_send_def]
QED

Theorem reading_create[local]:
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (INR ^missing_exc,st') ==>
  st'.gas_obs = []
Proof
  READING_WALK reading_base [eval_create_def, create_soft_failure_def]
QED

val reading_base = reading_raw_call :: reading_ext_call :: reading_send ::
                   reading_create :: reading_base;

Theorem reading_evaluator_primitives[local]:
  (lock_if_nr cx nr view st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (check_create_blueprint has_salt literal_offset vs st = (INR ^missing_exc,st') ==> st'.gas_obs = [])
Proof
  READING_WALK reading_base [lock_if_nr_def, check_create_blueprint_def]
QED

Theorem reading_create_operands[local]:
  eval_create_operands cx kind has_salt rof arg_tys literal_offset vs st =
    (INR ^missing_exc,st') ==> st'.gas_obs = []
Proof
  Cases_on `kind` >>
  READING_WALK (reading_evaluator_primitives :: reading_base)
    [eval_create_operands_def]
QED

val READING_CONSTRUCTOR_TAC =
  rpt READING_INTRO >> simp_tac bool_ss [Once evaluate_def,
    vyperContextTheory.is_self_codesize_def] >>
  READING_WALK (reading_create_operands :: reading_evaluator_primitives :: reading_base)
    [switch_BoolV_def];

Theorem evaluate_missing_reading_state:
  (!cx s st st'. eval_stmt cx s st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (!cx ss st st'. eval_stmts cx ss st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (!cx it st st'. eval_iterator cx it st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (!cx tyv id body vs st st'. eval_for cx tyv id body vs st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (!cx e st st'. eval_expr cx e st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (!cx es st st'. eval_exprs cx es st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (!cx t st st'. eval_base_place cx t st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (!cx t st st'. eval_target_place cx t st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (!cx g v st st'. assign_tuple_targets cx g v st = (INR ^missing_exc,st') ==> st'.gas_obs = []) /\
  (!cx gs vs st st'. assign_tuple_target_list cx gs vs st = (INR ^missing_exc,st') ==> st'.gas_obs = [])
Proof
  ho_match_mp_tac evaluate_ind >>
  map_every (fn n => conj_tac >- suspend ("c" ^ Int.toString n))
    (List.tabulate (60, fn n => n + 1)) >> suspend "c61"
QED

Resume evaluate_missing_reading_state[c1]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c2]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c3]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c4]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c5]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c6]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c7]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c8]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c9]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c10]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c11]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c12]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c13]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c14]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c15]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c16]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c17]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c18]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c19]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c20]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c21]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c22]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c23]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c24]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c25]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c26]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c27]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c28]:
  READING_CONSTRUCTOR_TAC >> metis_tac[]
QED
Resume evaluate_missing_reading_state[c29]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c30]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c31]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c32]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c33]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c34]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c35]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c36]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c37]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c38]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c39]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c40]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c41]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c42]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c43]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c44]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c45]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c46]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c47]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c48]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c49]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c50]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c51]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c52]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c53]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c54]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c55]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c56]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c57]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c58]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c59]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c60]:
  READING_CONSTRUCTOR_TAC
QED
Resume evaluate_missing_reading_state[c61]:
  rpt conj_tac >> READING_CONSTRUCTOR_TAC
QED

Finalise evaluate_missing_reading_state
