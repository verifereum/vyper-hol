(* TOP-LEVEL: ABI encoders may change memory, SSA bindings, allocation records
   and control position. Every other state component, including existing logs,
   accounts, pending deletions, call context and outcome supply, is preserved. *)
Theory abiStateFrame
Ancestors
  venomState venomExecSemantics finite_map list words

Definition abi_state_context_def:
  abi_state_context ss = ss with <|
    vs_memory := []; vs_vars := FEMPTY; vs_prev_bb := NONE;
    vs_current_bb := ""; vs_inst_idx := 0;
    vs_allocas := FEMPTY; vs_alloca_next := 0 |>
End

Definition abi_state_frame_def:
  abi_state_frame before after <=> abi_state_context after = abi_state_context before
End

Theorem abi_state_context_mutable[simp]:
  !ss mem vars prev bb index allocas next.
    abi_state_context (ss with vs_memory := mem) = abi_state_context ss /\
    abi_state_context (ss with vs_vars := vars) = abi_state_context ss /\
    abi_state_context (ss with vs_prev_bb := prev) = abi_state_context ss /\
    abi_state_context (ss with vs_current_bb := bb) = abi_state_context ss /\
    abi_state_context (ss with vs_inst_idx := index) = abi_state_context ss /\
    abi_state_context (ss with vs_allocas := allocas) = abi_state_context ss /\
    abi_state_context (ss with vs_alloca_next := next) = abi_state_context ss
Proof
  simp[abi_state_context_def, venom_state_component_equality]
QED

Theorem abi_state_frame_refl[simp]:
  !ss. abi_state_frame ss ss
Proof
  simp[abi_state_frame_def]
QED

Theorem abi_state_frame_sym:
  !before after. abi_state_frame before after ==> abi_state_frame after before
Proof
  simp[abi_state_frame_def]
QED

Theorem abi_state_frame_trans:
  !before middle after.
    abi_state_frame before middle /\ abi_state_frame middle after ==> abi_state_frame before after
Proof
  simp[abi_state_frame_def]
QED

Theorem abi_state_context_primitives[simp]:
  !ss name value offset bytes src count label.
    abi_state_context (update_var name value ss) = abi_state_context ss /\
    abi_state_context (mstore offset value ss) = abi_state_context ss /\
    abi_state_context (write_memory_with_expansion offset bytes ss) = abi_state_context ss /\
    abi_state_context (mcopy offset src count ss) = abi_state_context ss /\
    abi_state_context (jump_to label ss) = abi_state_context ss
Proof
  simp[update_var_def, mstore_def, write_memory_with_expansion_def, mcopy_def, jump_to_def, LET_THM]
QED

Theorem abi_state_frame_observables:
  !before after. abi_state_frame before after ==>
    after.vs_logs = before.vs_logs /\ after.vs_call_ctx = before.vs_call_ctx /\
    after.vs_accounts = before.vs_accounts /\ after.vs_transient = before.vs_transient /\
    after.vs_pending_deletions = before.vs_pending_deletions /\
    after.vs_immutables = before.vs_immutables /\ after.vs_requests = before.vs_requests /\
    after.vs_outcomes = before.vs_outcomes /\ after.vs_returndata = before.vs_returndata /\
    after.vs_halted = before.vs_halted
Proof
  simp_tac (srw_ss()) [abi_state_frame_def, abi_state_context_def, venom_state_component_equality] >>
  rpt strip_tac >> simp[]
QED
