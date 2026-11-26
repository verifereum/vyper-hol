(* Instantiate the shared evaluator frame walk with the ordered record invariant. *)
Theory s1PrefixOrderedEval
Ancestors
  s1PrefixOutcomeEvents vyperState vyperInterpreter vyperCreate vyperCallOutcome
  vyperCallOutcomeFrame extCallOracle vyperStatePreservation vyperPlaceFrames
  vyperMachineFrame list pair sum option
Libs monadsyntax s1PrefixRequestFrameLib

structure RF = s1PrefixRequestFrameLib

Definition ordered_record_frame_def[local]:
  ordered_record_frame f <=>
    state_rel_frame
      (\s t. prefix_record_ok s.requests s.storage_trace ==>
             prefix_record_ok t.requests t.storage_trace) f
End

val frame_def = ordered_record_frame_def
val updates = CONJUNCTS prefix_record_ok_updates
val nonoutcome = LIST_CONJ (List.take (tl updates, 3))
val paired = List.last updates

Theorem ordered_record_frame_result[local]:
  ordered_record_frame f /\ f st = (res,st') /\
  prefix_record_ok st.requests st.storage_trace ==>
  prefix_record_ok st'.requests st'.storage_trace
Proof
  simp[frame_def, state_rel_frame_result] >> metis_tac[]
QED

Theorem ordered_bind[local]:
  ordered_record_frame f /\
  (!v. (?s t. f s = (INL v,t)) ==> ordered_record_frame (g v)) ==>
  ordered_record_frame (bind f g)
Proof
  RF.bind_tac frame_def
QED

Theorem ordered_try[local]:
  ordered_record_frame f /\ (!e. ordered_record_frame (h e)) ==>
  ordered_record_frame (try f h)
Proof
  RF.try_tac frame_def
QED

Theorem ordered_finally[local]:
  ordered_record_frame f /\ ordered_record_frame h ==>
  ordered_record_frame (finally f h)
Proof
  RF.finally_tac frame_def
QED

Theorem ordered_finally_unless_halt[local]:
  ordered_record_frame f /\ ordered_record_frame h ==>
  ordered_record_frame (finally_unless_halt f h)
Proof
  RF.finally_unless_halt_tac frame_def
QED

Theorem ordered_choice[local]:
  (b ==> ordered_record_frame f) /\ (~b ==> ordered_record_frame g) ==>
  ordered_record_frame (if b then f else g)
Proof
  RF.choice_tac
QED

Theorem ordered_primitives[local]:
  ordered_record_frame (return v) /\
  ordered_record_frame (\s. return (f s) s) /\
  ordered_record_frame (\s. (INL (IS_SOME s.outcomes),s)) /\
  ordered_record_frame (raise e) /\
  ordered_record_frame (type_check b msg) /\
  ordered_record_frame (check b msg) /\
  ordered_record_frame (check_not_static cx) /\
  ordered_record_frame (lift_option opt msg) /\
  ordered_record_frame (lift_option_type opt msg) /\
  ordered_record_frame (lift_sum sum) /\
  ordered_record_frame (lift_sum_runtime rs) /\
  ordered_record_frame get_accounts /\
  ordered_record_frame get_transient_storage /\
  ordered_record_frame get_pending_deletions /\
  ordered_record_frame get_scopes /\
  ordered_record_frame (update_accounts fa) /\
  ordered_record_frame (update_transient ft) /\
  ordered_record_frame (update_pending_deletions fp) /\
  ordered_record_frame (push_log lg) /\
  ordered_record_frame (append_logs ls) /\
  ordered_record_frame (set_scopes scs) /\
  ordered_record_frame push_scope /\
  ordered_record_frame (push_scope_with_var nm ty value) /\
  ordered_record_frame (set_address_immutables cx imms) /\
  ordered_record_frame pop_scope /\
  ordered_record_frame (push_function fn sc cx) /\
  ordered_record_frame (pop_function scs) /\
  ordered_record_frame next_gas_reading /\
  ordered_record_frame record_storage_backend /\
  ordered_record_frame (record_storage_event (StorageRoot b' slot ty)) /\
  ordered_record_frame (record_storage_event (StorageLock slot))
Proof
  RF.primitives_tac frame_def nonoutcome
QED

Theorem ordered_take_request[local]:
  ordered_record_frame (take_request_outcome rq)
Proof
  RF.take_request_tac frame_def paired
QED

Theorem ordered_take_create[local]:
  ordered_record_frame (take_create_outcome kind amount code)
Proof
  RF.take_create_tac frame_def paired
QED

Theorem ordered_take[local]:
  ordered_record_frame (take_call_outcome gas_cap target data value) /\
  ordered_record_frame (take_delegate_outcome gas_cap target data value)
Proof
  RF.take_tac frame_def ordered_take_request
QED

Theorem ordered_adopt[local]:
  ordered_record_frame (adopt_call_outcome rq outcome)
Proof
  RF.adopt_tac frame_def nonoutcome
QED

Theorem ordered_unchanged[local]:
  (!s res t. f s = (res,t) ==> t = s) ==> ordered_record_frame f
Proof
  RF.state_unchanged_tac frame_def
QED

Theorem ordered_read_result[local]:
  ordered_record_frame (read_result cx result)
Proof
  RF.read_result_tac ordered_unchanged
QED

Theorem ordered_reads[local]:
  ordered_record_frame (read_place cx p) /\
  ordered_record_frame (place_type_value cx p) /\
  ordered_record_frame (read_results cx results) /\
  ordered_record_frame (conditional_result cx result) /\
  ordered_record_frame (get_place result)
Proof
  RF.reads_tac ordered_unchanged
QED

val ordered_rules = [ordered_bind, ordered_try, ordered_finally,
                     ordered_finally_unless_halt, ordered_choice]
val step = RF.primitive_step ordered_rules
val primitives = [ordered_primitives, ordered_reads, ordered_read_result,
                  ordered_take, ordered_take_create, ordered_adopt]

Theorem ordered_storage_backend[local]:
  ordered_record_frame (get_storage_backend cx transient) /\
  ordered_record_frame (set_storage_backend cx transient backend)
Proof
  RF.storage_backend_tac (step primitives)
QED

Theorem ordered_address_immutables[local]:
  ordered_record_frame (get_address_immutables cx)
Proof
  RF.address_immutables_tac frame_def
QED

val storage = ordered_storage_backend :: ordered_address_immutables :: primitives

Theorem ordered_resolve_array[local]:
  ordered_record_frame (resolve_array_element cx tr slot ty subs)
Proof
  RF.resolve_array_tac ordered_unchanged
QED

Theorem ordered_storage_locals[local]:
  ordered_record_frame (write_place cx place v) /\
  ordered_record_frame (lookup_flag_mem cx nsid mid) /\
  ordered_record_frame (set_variable nm v) /\
  ordered_record_frame (lookup_global cx src nm) /\
  ordered_record_frame (set_global cx src nm v)
Proof
  RF.storage_and_locals_tac (step storage)
QED

Theorem ordered_extend_storage[local]:
  !cx tr slot ty sb. ordered_record_frame (extend_storage_place cx tr slot ty sb)
Proof
  RF.extend_storage_tac (step (ordered_resolve_array :: storage))
QED

Theorem ordered_extend_place[local]:
  !cx result sb. ordered_record_frame (extend_place cx result sb)
Proof
  RF.extend_place_tac (step (ordered_extend_storage :: storage))
QED

Theorem ordered_select[local]:
  !cx ty result sb. ordered_record_frame (select_result cx ty result sb)
Proof
  RF.select_tac (step (ordered_extend_place :: storage))
QED

Theorem ordered_array_length[local]:
  !cx result. ordered_record_frame (result_array_length cx result)
Proof
  RF.array_length_tac (step storage)
QED

val places = [ordered_storage_locals, ordered_extend_place,
              ordered_select, ordered_array_length] @ storage

Theorem ordered_append_place[local]:
  !cx place v. ordered_record_frame (append_place cx place v)
Proof
  RF.append_place_tac (step places)
QED

Theorem ordered_pop_place[local]:
  !cx place. ordered_record_frame (pop_place cx place)
Proof
  RF.pop_place_tac (step places)
QED

Theorem ordered_raw_call[local]:
  ordered_record_frame (eval_raw_call cx flags target calldata amount gas)
Proof
  RF.raw_call_tac (step primitives)
QED

Theorem ordered_ext_call[local]:
  ordered_record_frame (eval_ext_call cx static_flag skip_check sigt opts vs)
Proof
  RF.ext_call_tac ordered_rules primitives
QED

Theorem ordered_send[local]:
  ordered_record_frame (eval_send cx gas vs)
Proof
  RF.send_tac (step primitives)
QED

Theorem ordered_create_oracle[local]:
  ordered_record_frame (create_oracle_result salt value initcode rof)
Proof
  RF.create_oracle_tac frame_def ordered_record_frame_result
    ordered_take_create ordered_adopt
QED

Theorem ordered_create[local]:
  ordered_record_frame (eval_create cx kind has_salt rof arg_tys vs blueprint_size)
Proof
  RF.create_tac (step (ordered_create_oracle :: primitives))
QED

Theorem ordered_precompile[local]:
  ordered_record_frame (precompile_call_success bt vs)
Proof
  RF.precompile_tac frame_def ordered_record_frame_result ordered_take
QED

Theorem ordered_handle_function[local]:
  ordered_record_frame (handle_function ex)
Proof
  RF.handle_function_tac (step primitives)
QED

val ORDERED_EVAL_CASE = RF.evaluate_case ordered_rules
  ([ordered_precompile, ordered_raw_call, ordered_ext_call, ordered_send,
    ordered_create, ordered_handle_function, ordered_append_place,
    ordered_pop_place] @ places)

Theorem ordered_eval[local]:
  (!cx s. ordered_record_frame (eval_stmt cx s)) /\
  (!cx ss. ordered_record_frame (eval_stmts cx ss)) /\
  (!cx it. ordered_record_frame (eval_iterator cx it)) /\
  (!cx tyv nm body vs. ordered_record_frame (eval_for cx tyv nm body vs)) /\
  (!cx e. ordered_record_frame (eval_expr cx e)) /\
  (!cx es. ordered_record_frame (eval_exprs cx es)) /\
  (!cx t. ordered_record_frame (eval_base_place cx t)) /\
  (!cx t. ordered_record_frame (eval_target_place cx t)) /\
  (!cx t v. ordered_record_frame (assign_tuple_targets cx t v)) /\
  (!cx ts vs. ordered_record_frame (assign_tuple_target_list cx ts vs))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> ORDERED_EVAL_CASE
QED

Theorem prefix_record_entry_frames:
  (!cx body. state_rel_frame
    (\s t. prefix_record_ok s.requests s.storage_trace ==>
           prefix_record_ok t.requests t.storage_trace) (eval_stmts cx body)) /\
  (!cx ds. state_rel_frame
    (\s t. prefix_record_ok s.requests s.storage_trace ==>
           prefix_record_ok t.requests t.storage_trace) (eval_exprs cx ds)) /\
  (!mut cx. state_rel_frame
    (\s t. prefix_record_ok s.requests s.storage_trace ==>
           prefix_record_ok t.requests t.storage_trace) (send_call_value mut cx)) /\
  (!cx nr view. state_rel_frame
    (\s t. prefix_record_ok s.requests s.storage_trace ==>
           prefix_record_ok t.requests t.storage_trace) (lock_if_nr cx nr view)) /\
  (!cx nr view. state_rel_frame
    (\s t. prefix_record_ok s.requests s.storage_trace ==>
           prefix_record_ok t.requests t.storage_trace) (unlock_if_nr cx nr view))
Proof
  simp_tac bool_ss [GSYM frame_def, ordered_eval] >>
  rpt conj_tac >> rpt (step primitives)
QED
