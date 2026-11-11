(* The machine-visible projection, independent of scopes and oracle bookkeeping. *)
Theory vyperMachineFrame
Ancestors
  vyperState vyperCallOutcome vyperInterpreter vyperCallOutcomeFrame
  vyperStatePreservation

Definition machine_frame_def:
  machine_frame (s:evaluation_state) (t:evaluation_state) <=>
    t.accounts = s.accounts /\ t.tStorage = s.tStorage /\
    t.immutables = s.immutables /\ t.logs = s.logs /\
    t.pending_deletions = s.pending_deletions
End

Theorem machine_frame_refl[simp]:
  machine_frame s s
Proof
  simp[machine_frame_def]
QED

Theorem machine_frame_trans:
  machine_frame s t /\ machine_frame t u ==> machine_frame s u
Proof
  simp[machine_frame_def]
QED

Theorem machine_frame_reconstruct:
  machine_frame (initial_state am scs) st ==>
  abstract_machine_from_state am.sources am.exports am.layouts st = am
Proof
  simp[machine_frame_def, initial_state_def, abstract_machine_from_state_def,
       abstract_machine_component_equality]
QED

Theorem machine_frame_scopes[simp]:
  machine_frame s (s with scopes := scs)
Proof
  simp[machine_frame_def]
QED

Theorem machine_frame_oracle[simp]:
  machine_frame s (s with <|outcomes := os; requests := rqs|>)
Proof
  simp[machine_frame_def]
QED

(* Relation transport retaining the actual intermediate state of a bind. *)
Theorem state_rel_bind_pointwise:
  (!x y z. R x y /\ R y z ==> R x z) /\
  R s (SND (f s)) /\
  (!v t. f s = (INL v,t) ==> R t (SND (g v t))) ==>
  R s (SND (vyperState$bind f g s))
Proof
  strip_tac >> Cases_on `f s` >> rename1 `f s = (answer,t)` >>
  Cases_on `answer` >> gvs[bind_def] >>
  first_x_assum irule >> goal_assum drule >> simp[]
QED

(* Generic exception and cleanup transport. *)
Theorem state_rel_frame_try:
  (!s t u. R s t /\ R t u ==> R s u) /\
  state_rel_frame R f /\ (!e. state_rel_frame R (h e)) ==>
  state_rel_frame R (try f h)
Proof
  simp[state_rel_frame_def, try_def] >> rpt strip_tac >>
  Cases_on `f st` >>
  qpat_x_assum `!st. R st (SND (f st))`
    (qspec_then `st` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `q` >> gvs[] >>
  first_x_assum irule >> goal_assum drule >> simp[]
QED

Theorem state_rel_frame_finally:
  (!s t u. R s t /\ R t u ==> R s u) /\
  state_rel_frame R f /\ state_rel_frame R g ==>
  state_rel_frame R (finally f g)
Proof
  simp[state_rel_frame_def, finally_def, ignore_bind_def, bind_def,
       return_def, raise_def] >> rpt strip_tac >>
  Cases_on `f st` >>
  qpat_x_assum `!st. R st (SND (f st))`
    (qspec_then `st` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `g r` >>
  qpat_x_assum `!st. R st (SND (g st))`
    (qspec_then `r` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `q` >> Cases_on `q'` >> gvs[] >>
  first_x_assum irule >> goal_assum drule >> simp[]
QED

(* IntCall's cleanup is skipped when the body halts. *)
Theorem state_rel_frame_finally_unless_halt:
  (!s t u. R s t /\ R t u ==> R s u) /\
  state_rel_frame R f /\ state_rel_frame R g ==>
  state_rel_frame R (finally_unless_halt f g)
Proof
  simp[state_rel_frame_def] >> rpt strip_tac >>
  simp[finally_unless_halt_def] >>
  Cases_on `f st` >> rename1 `f st = (q, r)` >>
  `R st r` by
    (qpat_x_assum `!st. R st (SND (f st))` (qspec_then `st` mp_tac) >>
     simp[]) >>
  `R r (SND (g r))` by simp[] >>
  Cases_on `q` >> TRY (Cases_on `y`) >>
  simp[ignore_bind_def, bind_def, return_def, raise_def] >>
  Cases_on `g r` >> Cases_on `q` >> gvs[] >> metis_tac[]
QED

Theorem machine_frame_primitives:
  state_rel_frame machine_frame (vyperState$return x) /\
  state_rel_frame machine_frame (vyperState$raise e) /\
  state_rel_frame machine_frame (assert b ex) /\
  state_rel_frame machine_frame (check b msg) /\
  state_rel_frame machine_frame (type_check b msg) /\
  state_rel_frame machine_frame (lift_option opt msg) /\
  state_rel_frame machine_frame (lift_option_type opt msg) /\
  state_rel_frame machine_frame (lift_sum rs) /\
  state_rel_frame machine_frame (lift_sum_runtime rt) /\
  state_rel_frame machine_frame get_accounts /\
  state_rel_frame machine_frame get_transient_storage /\
  state_rel_frame machine_frame get_scopes /\
  state_rel_frame machine_frame (set_scopes scs) /\
  state_rel_frame machine_frame push_scope /\
  state_rel_frame machine_frame (push_scope_with_var nm tv v) /\
  state_rel_frame machine_frame pop_scope
Proof
  Cases_on `opt` >> Cases_on `rs` >> Cases_on `rt` >>
  simp[state_rel_frame_def, machine_frame_def, return_def, raise_def,
       assert_def, check_def, type_check_def, lift_option_def,
       lift_option_type_def, lift_sum_def, lift_sum_runtime_def,
       get_accounts_def, get_transient_storage_def, get_scopes_def,
       set_scopes_def, push_scope_def, push_scope_with_var_def, pop_scope_def] >>
  rpt strip_tac >> Cases_on `st.scopes` >> simp[return_def, raise_def]
QED

Theorem machine_frame_next_gas_reading:
  state_rel_frame machine_frame next_gas_reading
Proof
  simp[state_rel_frame_def, next_gas_reading_def] >> rpt strip_tac >>
  CASE_TAC >> simp[raise_def, return_def, machine_frame_def]
QED

Theorem machine_frame_precompile_call_success:
  state_rel_frame machine_frame (precompile_call_success bt)
Proof
  rw[state_rel_frame_def] >> Cases_on `precompile_call_success bt st` >>
  drule precompile_call_success_state >> rw[] >> simp[machine_frame_def]
QED

Theorem machine_frame_view_lock:
  state_rel_frame machine_frame (acquire_nonreentrant_lock addr slot T)
Proof
  simp[state_rel_frame_def, acquire_nonreentrant_lock_def, bind_def,
       get_transient_storage_def, return_def] >> gen_tac >>
  IF_CASES_TAC >> simp[return_def, raise_def]
QED

Theorem machine_frame_nonpayable_value:
  mut <> Payable ==> state_rel_frame machine_frame (send_call_value mut cx)
Proof
  strip_tac >> simp[state_rel_frame_def, send_call_value_def] >>
  Cases_on `cx.txn.value = 0` >>
  simp[ignore_bind_def, bind_def, check_def, assert_def, return_def]
QED

Theorem machine_frame_handlers:
  state_rel_frame machine_frame (handle_function ex) /\
  state_rel_frame machine_frame (handle_loop_exception ex)
Proof
  Cases_on `ex` >>
  simp[state_rel_frame_def, handle_function_def, handle_loop_exception_def,
       return_def, raise_def]
QED

Theorem machine_frame_new_variable:
  state_rel_frame machine_frame (new_variable nm tv v)
Proof
  simp[state_rel_frame_def, new_variable_def, get_scopes_def, bind_def,
       ignore_bind_def, type_check_def, assert_def, return_def] >>
  gen_tac >> Cases_on `lookup_scopes nm st.scopes = NONE` >>
  simp[raise_def] >> Cases_on `st.scopes` >>
  simp[set_scopes_def, return_def, raise_def]
QED


Theorem machine_frame_read_place:
  state_rel_frame machine_frame (read_place cx p)
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  drule read_place_state >> simp[]
QED

Theorem machine_frame_place_type_value:
  state_rel_frame machine_frame (place_type_value cx p)
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  drule place_type_value_state >> simp[]
QED

Theorem machine_frame_read_result:
  state_rel_frame machine_frame (read_result cx r)
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  drule read_result_state >> simp[]
QED

Theorem machine_frame_array_iterator_results:
  state_rel_frame machine_frame (array_iterator_results cx ty r)
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  drule array_iterator_results_state >> simp[]
QED

Theorem machine_frame_read_results:
  state_rel_frame machine_frame (read_results cx rs)
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  drule read_results_state >> simp[]
QED

Theorem machine_frame_lookup_global:
  state_rel_frame machine_frame (lookup_global cx src id)
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  drule lookup_global_state >> simp[]
QED

Theorem machine_frame_push_function:
  state_rel_frame machine_frame (push_function src_fn sc cx)
Proof
  simp[state_rel_frame_def, push_function_def, return_def]
QED

Theorem machine_frame_pop_function:
  state_rel_frame machine_frame (pop_function prev)
Proof
  simp[pop_function_def, machine_frame_primitives]
QED

Theorem machine_frame_reads:
  state_rel_frame machine_frame (lookup_global cx src id) /\
  state_rel_frame machine_frame (lookup_flag_mem cx nsid mid) /\
  state_rel_frame machine_frame (read_storage_slot cx tr slot ty) /\
  state_rel_frame machine_frame (result_array_length cx r)
Proof
  simp[state_rel_frame_result] >> metis_tac[lookup_global_state,
    lookup_flag_mem_state, read_storage_slot_state,
    result_array_length_state, machine_frame_refl]
QED

Theorem machine_frame_unchanged_reads:
  state_rel_frame machine_frame (conditional_result cx r) /\
  state_rel_frame machine_frame (check_not_static cx) /\
  state_rel_frame machine_frame (check_create_blueprint has_salt vs)
Proof
  simp[state_rel_frame_result] >>
  metis_tac[conditional_result_state, vyperCreateTheory.check_create_blueprint_state,
    check_not_static_eq, pairTheory.PAIR_EQ, pairTheory.SND, machine_frame_refl]
QED

Theorem machine_frame_get_place:
  state_rel_frame machine_frame (get_place r)
Proof
  Cases_on `r` >> simp[get_place_def, state_rel_frame_def, return_def, raise_def]
QED

Theorem machine_frame_bind:
  state_rel_frame machine_frame f /\
  (!v. state_rel_frame machine_frame (g v)) ==>
  state_rel_frame machine_frame (vyperState$bind f g)
Proof
  strip_tac >> irule state_rel_frame_bind_guarded >>
  simp[] >> metis_tac[machine_frame_trans]
QED

Theorem machine_frame_extend_storage_place:
  state_rel_frame machine_frame (extend_storage_place cx tr slot tv sb)
Proof
  Cases_on `sb`
  >~ [`ValueSubscript v`] >-
    (Cases_on `v` >> Cases_on `tv` >>
     simp[extend_storage_place_def, state_rel_frame_result, raise_def,
          bind_def, ignore_bind_def, check_def, assert_def,
          lift_option_type_def, return_def, AllCaseEqs()] >>
     rpt strip_tac >> imp_res_tac resolve_array_element_state >> gvs[] >>
     rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
     pairarg_tac >> gvs[return_def]) >>
  Cases_on `tv` >>
  simp[extend_storage_place_def, state_rel_frame_result, raise_def,
       bind_def, lift_option_type_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  pairarg_tac >> gvs[return_def]
QED

Theorem machine_frame_extend_place:
  state_rel_frame machine_frame (extend_place cx r sb)
Proof
  Cases_on `r` >> simp[extend_place_def, machine_frame_primitives]
  >~ [`PlaceR p`] >-
    (Cases_on `p` >> simp[extend_place_def] >>
     rpt (simp[ignore_bind_def] >> match_mp_tac machine_frame_bind >> conj_tac >-
       simp[machine_frame_primitives, machine_frame_place_type_value,
            machine_frame_read_place, machine_frame_extend_storage_place] >>
       gen_tac) >>
     simp[state_rel_frame_def, return_def]) >>
  Cases_on `sb` >> Cases_on `v` >>
  simp[extend_place_def, state_rel_frame_def, bind_def,
       lift_option_type_def, return_def, raise_def] >>
  gen_tac >> rpt (BasicProvers.FULL_CASE_TAC >> simp[return_def, raise_def])
QED

Theorem machine_frame_select_result:
  state_rel_frame machine_frame (select_result cx ty r sb)
Proof
  Cases_on `r` >> simp[select_result_def, machine_frame_extend_place] >>
  rpt (simp[ignore_bind_def] >> match_mp_tac machine_frame_bind >>
       conj_tac >- simp[machine_frame_primitives] >> gen_tac) >>
  simp[state_rel_frame_def, return_def]
QED

Theorem machine_frame_write_memory_place:
  state_rel_frame machine_frame (write_place cx (MemoryPlace id path) v)
Proof
  simp[write_place_def, state_rel_frame_def, get_scopes_def, bind_def,
       ignore_bind_def, lift_option_type_def, lift_sum_def,
       type_check_def, assert_def, set_scopes_def, return_def] >>
  gen_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  PairCases_on `x` >>
  gvs[bind_def, ignore_bind_def, assert_def, set_scopes_def,
      lift_sum_def, return_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  gvs[bind_def, ignore_bind_def, set_scopes_def, return_def]
QED

Theorem machine_frame_append_memory_place:
  state_rel_frame machine_frame (append_place cx (MemoryPlace id path) v)
Proof
  simp[append_place_def] >>
  rpt (simp[] >> match_mp_tac machine_frame_bind >> conj_tac >-
    simp[machine_frame_place_type_value, machine_frame_read_place,
         machine_frame_primitives] >> gen_tac) >>
  simp[machine_frame_write_memory_place]
QED

Theorem machine_frame_pop_memory_place:
  state_rel_frame machine_frame (pop_place cx (MemoryPlace id path))
Proof
  simp[pop_place_def] >>
  match_mp_tac machine_frame_bind >> conj_tac
  >- simp[machine_frame_primitives] >>
  gen_tac >> simp[] >> match_mp_tac machine_frame_bind >> conj_tac
  >- simp[machine_frame_primitives] >>
  qx_gen_tac `scope_parts` >> PairCases_on `scope_parts` >>
  simp[ignore_bind_def] >>
  rpt (simp[] >> match_mp_tac machine_frame_bind >> conj_tac
       >- simp[machine_frame_primitives] >> gen_tac) >>
  qmatch_goalsub_abbrev_tac `UNCURRY continuation parts` >>
  PairCases_on `parts` >> simp[Abbr `continuation`] >>
  match_mp_tac machine_frame_bind >>
  simp[machine_frame_primitives, state_rel_frame_def, return_def]
QED
