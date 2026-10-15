(* Oracle-field representation contracts; no call semantics activation.
 * TOP-LEVEL: residual projections/update transport, primitive commutation,
 * nonempty setup/merge regressions. All lists remain universally quantified.
 *)
Theory oracleStateProps
Ancestors
  venomState venomInst venomExecSemantics stateFrame calleeTransport

(* ===== Residual frames retain both lists ===== *)

Theorem oracle_frame_projection[simp]:
  (state_frame s).vs_outcomes = s.vs_outcomes /\
  (state_frame s).vs_requests = s.vs_requests /\
  (execution_frame s).vs_outcomes = s.vs_outcomes /\
  (execution_frame s).vs_requests = s.vs_requests
Proof
  simp[state_frame_def, execution_frame_def]
QED

Theorem oracle_frame_updates[simp]:
  state_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    state_frame s with <| vs_outcomes := os; vs_requests := rqs |> /\
  execution_frame (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    execution_frame s with <| vs_outcomes := os; vs_requests := rqs |>
Proof
  simp[state_frame_def, execution_frame_def]
QED

Theorem oracle_state_frame_transport:
  state_frame s1 = state_frame s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  strip_tac >> conj_tac >> irule state_frame_projection >>
  simp_tac bool_ss [oracle_frame_projection] >> metis_tac[]
QED

Theorem oracle_execution_frame_transport:
  execution_frame s1 = execution_frame s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  strip_tac >> conj_tac >> irule execution_frame_projection >>
  simp_tac bool_ss [oracle_frame_projection] >> metis_tac[]
QED

(* ===== Updating oracle fields commutes with primitive state operations ===== *)

Theorem oracle_primitive_commute:
  update_var x v (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    update_var x v s with <| vs_outcomes := os; vs_requests := rqs |> /\
  write_memory offset bytes (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    write_memory offset bytes s with <| vs_outcomes := os; vs_requests := rqs |> /\
  expand_memory n (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    expand_memory n s with <| vs_outcomes := os; vs_requests := rqs |> /\
  write_memory_with_expansion offset bytes
      (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    write_memory_with_expansion offset bytes s
      with <| vs_outcomes := os; vs_requests := rqs |> /\
  mstore offset v (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    mstore offset v s with <| vs_outcomes := os; vs_requests := rqs |> /\
  mstore8 offset v (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    mstore8 offset v s with <| vs_outcomes := os; vs_requests := rqs |> /\
  sstore key v (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    sstore key v s with <| vs_outcomes := os; vs_requests := rqs |> /\
  tstore key v (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    tstore key v s with <| vs_outcomes := os; vs_requests := rqs |> /\
  jump_to lbl (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    jump_to lbl s with <| vs_outcomes := os; vs_requests := rqs |> /\
  next_inst (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    next_inst s with <| vs_outcomes := os; vs_requests := rqs |> /\
  halt_state (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    halt_state s with <| vs_outcomes := os; vs_requests := rqs |> /\
  revert_state (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    revert_state s with <| vs_outcomes := os; vs_requests := rqs |> /\
  set_returndata rd (s with <| vs_outcomes := os; vs_requests := rqs |>) =
    set_returndata rd s with <| vs_outcomes := os; vs_requests := rqs |>
Proof
  simp[update_var_def, write_memory_def, expand_memory_def,
       write_memory_with_expansion_def, mstore_def, mstore8_def,
       sstore_def, tstore_def, jump_to_def, next_inst_def,
       halt_state_def, revert_state_def, set_returndata_def]
QED

(* ===== Nonempty regressions: no reliance on initial [] defaults ===== *)

Theorem setup_callee_nonempty_oracle:
  ?callee.
    setup_callee (fn with fn_blocks := [bb]) []
      (caller with <| vs_outcomes := outcome::os;
                     vs_requests := request::rqs |>) = SOME callee /\
    callee.vs_outcomes = outcome::os /\
    callee.vs_requests = request::rqs /\
    merge_callee_state
      (caller with <| vs_outcomes := outcome::os;
                     vs_requests := request::rqs |>) callee =
      (caller with <| vs_outcomes := outcome::os;
                     vs_requests := request::rqs |>)
Proof
  simp[setup_callee_def] >>
  simp[merge_callee_state_def, venom_state_component_equality]
QED

(* Distinct singleton/doubleton lists exercise copying FROM the callee;
   leaving the caller lists untouched cannot satisfy this equality. *)
Theorem merge_callee_nonempty_oracle:
  merge_callee_state
    (caller with <| vs_outcomes := [old]; vs_requests := [before] |>)
    (callee with <| vs_outcomes := [new; old];
                   vs_requests := [after; before] |>) =
  merge_callee_state caller callee
    with <| vs_outcomes := [new; old]; vs_requests := [after; before] |>
Proof
  simp[merge_callee_state_def]
QED
