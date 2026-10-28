(* Callee transport for venom_state, including oracle list fields.
 * TOP-LEVEL: setup/merge projections; merge identity and composition;
 * selector-parametric setup/adopt transport; output-binding projections.
 * Existing generic bind_outputs_preserves is reused from venomInstProofs1.
 * Concrete projection lists describe today's fields, not an exhaustive
 * future shared-state interface. Exact identities and arbitrary selectors
 * avoid enumerating newly inherited/copied fields.
 * Calls remain concrete; oracle fields are transported, not consumed.
 *)
Theory calleeTransport
Ancestors
  venomState venomExecSemantics venomInstProofs1

(* ===== Shared state and frame projections ===== *)

(* Setup inherits mutable shared state and read-only execution context.
   Merge copies only mutable shared state; it keeps caller-local context,
   including the caller's allocation frame (vs_allocas, vs_alloca_next). *)

Theorem setup_callee_shared_fields:
  setup_callee fn args caller = SOME callee ==>
  callee.vs_memory = caller.vs_memory /\
  callee.vs_transient = caller.vs_transient /\
  callee.vs_accounts = caller.vs_accounts /\
  callee.vs_returndata = caller.vs_returndata /\
  callee.vs_logs = caller.vs_logs /\
  callee.vs_immutables = caller.vs_immutables /\
  callee.vs_alloca_next = caller.vs_alloca_next /\
  callee.vs_call_ctx = caller.vs_call_ctx /\
  callee.vs_tx_ctx = caller.vs_tx_ctx /\
  callee.vs_block_ctx = caller.vs_block_ctx /\
  callee.vs_data_section = caller.vs_data_section /\
  callee.vs_labels = caller.vs_labels /\
  callee.vs_code = caller.vs_code /\
  callee.vs_prev_hashes = caller.vs_prev_hashes /\
  callee.vs_initial_fmp = caller.vs_initial_fmp
Proof
  rw[setup_callee_def] >> gvs[]
QED

Theorem merge_callee_shared_fields[simp]:
  (merge_callee_state caller callee).vs_memory = callee.vs_memory /\
  (merge_callee_state caller callee).vs_transient = callee.vs_transient /\
  (merge_callee_state caller callee).vs_accounts = callee.vs_accounts /\
  (merge_callee_state caller callee).vs_returndata = callee.vs_returndata /\
  (merge_callee_state caller callee).vs_logs = callee.vs_logs /\
  (merge_callee_state caller callee).vs_immutables = callee.vs_immutables
Proof
  simp[merge_callee_state_def]
QED

(* Caller-local fields remain caller-local, even if the callee differs. *)
Theorem merge_callee_local_fields[simp]:
  (merge_callee_state caller callee).vs_vars = caller.vs_vars /\
  (merge_callee_state caller callee).vs_params = caller.vs_params /\
  (merge_callee_state caller callee).vs_current_bb = caller.vs_current_bb /\
  (merge_callee_state caller callee).vs_prev_bb = caller.vs_prev_bb /\
  (merge_callee_state caller callee).vs_inst_idx = caller.vs_inst_idx /\
  (merge_callee_state caller callee).vs_halted = caller.vs_halted /\
  (merge_callee_state caller callee).vs_allocas = caller.vs_allocas /\
  (merge_callee_state caller callee).vs_alloca_next = caller.vs_alloca_next /\
  (merge_callee_state caller callee).vs_call_ctx = caller.vs_call_ctx /\
  (merge_callee_state caller callee).vs_tx_ctx = caller.vs_tx_ctx /\
  (merge_callee_state caller callee).vs_block_ctx = caller.vs_block_ctx /\
  (merge_callee_state caller callee).vs_data_section = caller.vs_data_section /\
  (merge_callee_state caller callee).vs_labels = caller.vs_labels /\
  (merge_callee_state caller callee).vs_code = caller.vs_code /\
  (merge_callee_state caller callee).vs_prev_hashes = caller.vs_prev_hashes /\
  (merge_callee_state caller callee).vs_initial_fmp = caller.vs_initial_fmp
Proof
  simp[merge_callee_state_def]
QED

Theorem merge_callee_state_oracle[simp]:
  (merge_callee_state caller callee).vs_outcomes = callee.vs_outcomes /\
  (merge_callee_state caller callee).vs_requests = callee.vs_requests
Proof
  simp[merge_callee_state_def]
QED

(* ===== Exact record transport ===== *)

Theorem merge_callee_state_id[simp]:
  merge_callee_state s s = s
Proof
  simp[merge_callee_state_def, venom_state_component_equality]
QED

(* Setup alone has no shared side effects; merging it back is identity.
   The proof deliberately does not use a fixed shared-field projection list.
   It also covers newly added fields if setup inherits and merge copies them. *)
Theorem setup_callee_merge_identity:
  setup_callee fn args caller = SOME callee ==>
  merge_callee_state caller callee = caller
Proof
  rw[setup_callee_def] >>
  gvs[merge_callee_state_def, venom_state_component_equality]
QED

(* Only the final callee supplies shared side effects. *)
Theorem merge_callee_state_compose[simp]:
  merge_callee_state (merge_callee_state caller middle) callee =
    merge_callee_state caller callee /\
  merge_callee_state caller (merge_callee_state middle callee) =
    merge_callee_state caller callee
Proof
  simp[merge_callee_state_def, venom_state_component_equality]
QED

(* ===== Selector-parametric transport ===== *)

(* A selector invariant under arbitrary fresh-frame updates is inherited by
   successful setup. This sufficient condition is stronger than preservation
   by setup's particular updates. New inherited fields can instantiate it
   without another callee case analysis or an expanded shared-field list. *)
Theorem setup_callee_projection:
  (!st vars params current idx prev halted allocas fmp entry token.
    project (st with <| vs_vars := vars; vs_params := params;
      vs_current_bb := current; vs_inst_idx := idx; vs_prev_bb := prev;
      vs_halted := halted; vs_allocas := allocas; vs_fmp := fmp;
      vs_call_entry_fmp := entry; vs_return_pc_token := token |>) =
    project st) ==>
  setup_callee fn args caller = SOME callee ==>
  project callee = project caller
Proof
  strip_tac >> rw[setup_callee_def] >> gvs[]
QED

Theorem setup_callee_oracle:
  setup_callee fn args caller = SOME callee ==>
  callee.vs_outcomes = caller.vs_outcomes /\
  callee.vs_requests = caller.vs_requests
Proof
  strip_tac >> conj_tac >>
  irule setup_callee_projection >> simp[] >> metis_tac[]
QED

(* NONE is identity; SOME changes only FMP. A selector of any other field
   satisfies the premise, including future shared fields. *)
Theorem adopt_return_fmp_projection:
  (!st value. project (st with vs_fmp := value) = project st) ==>
  project (adopt_return_fmp ir s) = project s
Proof
  strip_tac >> Cases_on `ir.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def]
QED

Theorem adopt_return_fmp_oracle[simp]:
  (adopt_return_fmp ir s).vs_outcomes = s.vs_outcomes /\
  (adopt_return_fmp ir s).vs_requests = s.vs_requests
Proof
  conj_tac >> irule adopt_return_fmp_projection >> simp[]
QED

Theorem bind_outputs_oracle:
  bind_outputs outs vals s = SOME s' ==>
  s'.vs_outcomes = s.vs_outcomes /\ s'.vs_requests = s.vs_requests
Proof
  strip_tac >> conj_tac >>
  irule bind_outputs_preserves >> simp[update_var_def] >> metis_tac[]
QED

(* Reuse the generic output-binding transport rather than reproving FOLDL
   preservation for every added field. This also exercises its interface. *)
Theorem bind_outputs_shared_fields:
  bind_outputs outs vals s = SOME s' ==>
  s'.vs_memory = s.vs_memory /\
  s'.vs_transient = s.vs_transient /\
  s'.vs_accounts = s.vs_accounts /\
  s'.vs_returndata = s.vs_returndata /\
  s'.vs_logs = s.vs_logs /\
  s'.vs_immutables = s.vs_immutables /\
  s'.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> rpt conj_tac >>
  irule bind_outputs_preserves >> simp[update_var_def] >> metis_tac[]
QED
