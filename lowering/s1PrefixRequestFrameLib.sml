(* Evaluator proof shared by the request-count and ordered-record frames.
 * Clients use a unary frame predicate defined as
 *   state_rel_frame (\s t. P s.requests s.storage_trace ==>
 *                         P t.requests t.storage_trace).
 * The client supplies this unfolding and the two right-append laws below.
 * Instantiate the staged walk with composition rules and proved leaves;
 * primitive_step also handles send_call_value, lock_if_nr and unlock_if_nr. *)
structure s1PrefixRequestFrameLib =
struct

open HolKernel boolLib bossLib
open pairTheory vyperStateTheory vyperInterpreterTheory vyperCreateTheory
open vyperCallOutcomeTheory vyperCallOutcomeFrameTheory extCallOracleTheory
open vyperStatePreservationTheory vyperPlaceFramesTheory vyperMachineFrameTheory

fun bind_tac frame_def =
  simp[frame_def] >> strip_tac >>
  irule state_rel_frame_bind_guarded >> simp[] >> metis_tac[];

fun try_tac frame_def =
  simp[frame_def] >> strip_tac >> irule state_rel_frame_try >> simp[];

fun finally_tac frame_def =
  simp[frame_def] >> strip_tac >> irule state_rel_frame_finally >> simp[];

fun finally_unless_halt_tac frame_def =
  simp[frame_def] >> strip_tac >> irule state_rel_frame_finally_unless_halt >> simp[];

val choice_tac = Cases_on `b` >> simp[];

(* nonoutcome supplies the three right-append rules for StorageRoot,
 * StorageLock and StorageBackend (or a common rule for all three). *)
fun primitives_tac frame_def nonoutcome =
  rpt conj_tac >> simp[frame_def, state_rel_frame_def,
    return_def, raise_def, type_check_def, check_def, assert_def,
    check_not_static_def, lift_option_def, lift_option_type_def,
    lift_sum_def, lift_sum_runtime_def, get_accounts_def,
    get_transient_storage_def, get_pending_deletions_def, get_scopes_def,
    update_accounts_def, update_transient_def, update_pending_deletions_def,
    push_log_def, append_logs_def, set_scopes_def, push_scope_def,
    push_scope_with_var_def, set_address_immutables_def, pop_scope_def,
    push_function_def, pop_function_def, next_gas_reading_def,
    record_storage_backend_def, record_storage_event_def] >>
  rpt strip_tac >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[return_def, raise_def, nonoutcome];

(* paired preserves P on appending (rq,co), provided that a computed
 * precompile's accounts and transient storage are the request's snapshots.
 * Keep the take_outcome equation from pairarg_tac until proving this guard. *)
fun paired_tac paired =
  strip_tac >> irule paired >> simp[] >>
  metis_tac[computed_precompile_state,FST];

fun take_outcome_tac frame_def paired take_def =
  simp[frame_def, state_rel_frame_def] >>
  qx_gen_tac `st` >> Cases_on `st.outcomes` >> simp[take_def] >>
  rename1 `st.outcomes = SOME os` >> Cases_on `os` >>
  simp[take_def] >> pairarg_tac >>
  simp[record_request_def] >> IF_CASES_TAC >> simp[] >> paired_tac paired;

fun take_request_tac frame_def paired =
  take_outcome_tac frame_def paired take_request_outcome_def;

fun take_create_tac frame_def paired =
  take_outcome_tac frame_def paired take_create_outcome_def;

fun take_tac frame_def take_request =
  simp[frame_def, state_rel_frame_def,
       take_call_outcome_def, take_delegate_outcome_def] >>
  metis_tac[REWRITE_RULE[frame_def, state_rel_frame_def] (GEN_ALL take_request)];

fun adopt_tac frame_def nonoutcome =
  Cases_on `rq.cr_static` >> Cases_on `outcome.co_success` >>
  Cases_on `rq.cr_kind = MessageCall` >> Cases_on `rq.cr_kind = DelegateMessageCall` >>
  simp[frame_def, state_rel_frame_def, adopt_call_outcome_equation, nonoutcome];

fun state_unchanged_tac frame_def =
  simp[frame_def, state_rel_frame_result] >> metis_tac[];

fun read_result_tac unchanged = irule unchanged >> metis_tac[read_result_state];

fun reads_tac unchanged =
  rpt conj_tac >> irule unchanged >>
  metis_tac[read_place_state, place_type_value_state,
            read_results_state, conditional_result_state, get_place_state];

fun walk rules leaves unfolds =
  let
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

val common_unfolds =
  [ignore_bind_def, switch_BoolV_def, check_not_static_def,
   get_storage_backend_def, set_storage_backend_def, read_storage_slot_def,
   write_storage_slot_def, get_address_immutables_def, get_immutables_def,
   set_immutable_def, new_variable_def, transfer_value_def,
   send_call_value_def, frame_call_value_def, handle_loop_exception_def,
   handle_function_def, acquire_nonreentrant_lock_def,
   release_nonreentrant_lock_def, lock_if_nr_def, unlock_if_nr_def,
   create_soft_failure_def, check_create_blueprint_def];

fun primitive_step rules leaves = walk rules leaves common_unfolds;

fun storage_backend_tac step =
  Cases_on `transient` >> simp[get_storage_backend_def, set_storage_backend_def] >> rpt step;

fun address_immutables_tac frame_def =
  simp[frame_def, state_rel_frame_def,
       get_address_immutables_def, lift_option_type_def] >>
  qx_gen_tac `st` >> Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  simp[return_def, raise_def];

fun resolve_array_tac unchanged =
  irule unchanged >> metis_tac[resolve_array_element_state];

fun storage_and_locals_tac step =
  rpt conj_tac >>
  PURE_REWRITE_TAC[write_place_def, lookup_flag_mem_def, set_variable_def,
                   lookup_global_def, set_global_def]
  >- (Cases_on `place` >> pure_rewrite_tac[write_place_def] >> rpt step)
  >- (PairCases_on `nsid` >> pure_rewrite_tac[lookup_flag_mem_def] >> rpt step) >>
  rpt step;

fun recursive_tac ind def step =
  recInduct ind >> rpt strip_tac >> pure_rewrite_tac[def] >> rpt step;

val extend_storage_tac = recursive_tac extend_storage_place_ind extend_storage_place_def;
val extend_place_tac = recursive_tac extend_place_ind extend_place_def;
val select_tac = recursive_tac select_result_ind select_result_def;
val array_length_tac = recursive_tac result_array_length_ind result_array_length_def;
val append_place_tac = recursive_tac append_place_ind append_place_def;
val pop_place_tac = recursive_tac pop_place_ind pop_place_def;

fun raw_call_tac step = pure_rewrite_tac[eval_raw_call_def] >> rpt step;

fun ext_call_tac rules leaves =
  PairCases_on `sigt` >> Cases_on `vs` >> simp[eval_ext_call_def] >>
  rpt (walk rules leaves (eval_ext_call_effects_def :: common_unfolds));

fun send_tac step =
  namedCases_on `vs` ["", "target args"] >> simp[eval_send_def]
  >- rpt step >>
  Cases_on `args` >> simp[eval_send_def] >> rpt step;

(* result has premises frame f, f st = (res,st'), and P of st's lists,
 * in that order. The frame and execution equation fix the new state;
 * the goal context supplies the old list predicate. *)
fun result_tac result frame eq =
  let val step = MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] result)
                           (SPEC_ALL frame)
  in qpat_assum eq (mp_tac o MATCH_MP step) >> simp[] >> disch_tac end;

fun create_oracle_tac frame_def result take_create adopt =
  simp[frame_def, state_rel_frame_def] >>
  qx_gen_tac `st` >> strip_tac >>
  qabbrev_tac `kind = case salt of NONE => CreateCall | SOME s => Create2Call s` >>
  Cases_on `take_create_outcome kind value initcode st` >>
  rename1 `take_create_outcome kind value initcode st = (res,mid)` >>
  result_tac result take_create `take_create_outcome kind value initcode st = (res,mid)` >>
  pure_rewrite_tac[create_oracle_result_def] >> qpat_assum `Abbrev (kind = _)`
    (fn th => simp [GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
  namedCases_on `res` ["taken", "error"] >> gvs[] >>
  PairCases_on `taken` >>
  rename1 `take_create_outcome _ _ _ _ = (INL (request,outcome),mid)` >> simp[] >>
  Cases_on `adopt_call_outcome request outcome mid` >>
  rename1 `adopt_call_outcome request outcome mid = (answer,adopted)` >>
  result_tac result adopt `adopt_call_outcome request outcome mid = (answer,adopted)` >>
  rw[];

fun create_tac step = pure_rewrite_tac[eval_create_def] >> rpt step;

(* The precompile check changes neither recorded list after the take. *)
fun precompile_tac frame_def result take =
  rewrite_tac[frame_def, state_rel_frame_def] >>
  qx_gen_tac `st` >>
  Cases_on `precompile_builtin bt` >> simp[precompile_call_success_def, return_def] >>
  Cases_on `st.outcomes` >> simp[return_def] >>
  rename1 `st.outcomes = SOME os` >> Cases_on `os` >>
  simp[check_def, assert_def, return_def, raise_def] >> strip_tac >>
  Cases_on `take_call_outcome NONE (precompile_address bt) (precompile_input bt vs) NONE st` >>
  rename1 `take_call_outcome _ _ _ _ st = (res,mid)` >>
  result_tac result (CONJUNCT1 (SPEC_ALL take))
    `take_call_outcome _ _ _ _ st = (res,mid)` >>
  namedCases_on `res` ["taken", "error"] >> simp[bind_def, check_def, assert_def] >>
  PairCases_on `taken` >> simp[assert_def, return_def, raise_def] >> rw[];

fun handle_function_tac step =
  Cases_on `ex` >> simp[handle_function_def] >> rpt step;

fun evaluate_case rules leaves =
  evalWalkLib.EVAL_CASE (rpt strip_tac)
    (walk rules leaves ([conditional_result_def, array_iterator_results_def,
                         eval_create_operands_def] @ common_unfolds));

end
