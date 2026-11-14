(* Mutation primitives preserve the observation projection compositionally. *)
Theory guardMutationTrace
Ancestors
  pair vyperCallOutcomeFrame vyperState

Theorem trace_primitives[local]:
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (vyperState$return v) /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (vyperState$raise e) /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (check b msg) /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (type_check b msg) /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (lift_option opt msg) /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (lift_option_type opt msg) /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (lift_sum rs) /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) get_scopes /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (set_scopes sc) /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (get_immutables cx src) /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (set_immutable cx src id tv value) /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (get_storage_backend cx tr) /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (set_storage_backend cx tr storage) /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (check_not_static cx)
Proof
  Cases_on `tr` >>
  simp[state_rel_frame_def, return_def, raise_def, check_def, type_check_def,
       assert_def, lift_option_def, lift_option_type_def, lift_sum_def,
       get_scopes_def, set_scopes_def, get_immutables_def, set_immutable_def,
       get_address_immutables_def, set_address_immutables_def,
       get_storage_backend_def, set_storage_backend_def,
       get_accounts_def, get_transient_storage_def, update_accounts_def,
       update_transient_def, check_not_static_def, bind_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])
QED

val trace_bind = state_rel_frame_bind_guarded |>
  Q.INST [`R` |-> `\s t. t.storage_trace = s.storage_trace`] |> SRULE [];

Theorem trace_read[local]:
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (read_place cx p) /\
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (place_type_value cx p)
Proof
  simp[state_rel_frame_result] >> metis_tac[read_place_state, place_type_value_state]
QED

val TRACE_STEP = FIRST [
  FIRST (map MATCH_ACCEPT_TAC (CONJUNCTS trace_primitives)),
  FIRST (map MATCH_ACCEPT_TAC (CONJUNCTS trace_read)),
  MATCH_MP_TAC trace_bind >> conj_tac,
  gen_tac, strip_tac,
  CHANGED_TAC (simp_tac bool_ss [FORALL_PROD, LET_THM, ignore_bind_def,
                                UNCURRY, pair_case_thm])];

Theorem write_storage_trace[local]:
  state_rel_frame (\s t. t.storage_trace = s.storage_trace)
    (write_storage_slot cx tr slot tv v)
Proof
  simp_tac bool_ss [write_storage_slot_def] >> rpt TRACE_STEP
QED

Theorem write_place_trace[local]:
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (write_place cx p v)
Proof
  Cases_on `p` >> simp_tac bool_ss [write_place_def] >>
  rpt (FIRST [MATCH_ACCEPT_TAC write_storage_trace, TRACE_STEP])
QED

Theorem write_place_trace_unchanged:
  write_place cx p v st = (res,st') ==> st'.storage_trace = st.storage_trace
Proof
  strip_tac >>
  mp_tac (SRULE [state_rel_frame_result] write_place_trace) >>
  disch_then drule >> simp[]
QED

Theorem pop_place_trace[local]:
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (pop_place cx p)
Proof
  Cases_on `p` >>
  TRY (rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
       TRY (rename1 `ArrayTV tv bd` >> Cases_on `bd`)) >>
  simp_tac bool_ss [pop_place_def] >>
  rpt (FIRST [MATCH_ACCEPT_TAC write_storage_trace, TRACE_STEP])
QED

Theorem pop_place_trace_unchanged:
  pop_place cx p st = (res,st') ==> st'.storage_trace = st.storage_trace
Proof
  strip_tac >>
  mp_tac (SRULE [state_rel_frame_result] pop_place_trace) >>
  disch_then drule >> simp[]
QED

Theorem append_place_trace[local]:
  state_rel_frame (\s t. t.storage_trace = s.storage_trace) (append_place cx p v)
Proof
  Cases_on `p` >>
  TRY (rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
       TRY (rename1 `ArrayTV tv bd` >> Cases_on `bd`)) >>
  simp_tac bool_ss [append_place_def] >>
  rpt (FIRST [MATCH_ACCEPT_TAC write_storage_trace,
              MATCH_ACCEPT_TAC write_place_trace, TRACE_STEP])
QED

Theorem append_place_trace_unchanged:
  append_place cx p v st = (res,st') ==> st'.storage_trace = st.storage_trace
Proof
  strip_tac >>
  mp_tac (SRULE [state_rel_frame_result] append_place_trace) >>
  disch_then drule >> simp[]
QED
