(*
 * Per-Opcode State Preservation Lemmas
 *
 * Classifies opcodes by their effect on state and provides preservation
 * lemmas for pass correctness proofs.
 *
 * SCOPE: All theorems are about step_inst (full instruction semantics
 * including INVOKE).  For non-INVOKE opcodes, step_inst agrees with
 * step_inst_base (step_inst_non_invoke).  For INVOKE, preservation
 * follows from merge_callee_state + bind_outputs preserving caller
 * fields, or is excluded by the precondition (is_effect_free_op etc.).
 *
 * TOP-LEVEL:
 *   Classification:
 *     is_effect_free_op  — opcode has no side effects (only assigns output var)
 *     is_mem_write_op    — opcode writes memory (+ possibly output var)
 *     is_alloca_op       — allocation opcodes (memory + allocas)
 *     is_ext_call_op     — external calls (multiple state fields)
 *
 *   Helper preservation (exec_pure/read/write level):
 *     exec_pure1_state_equiv, exec_pure2_state_equiv, exec_pure3_state_equiv
 *     exec_read0_state_equiv, exec_read1_state_equiv
 *     exec_write2_preserves_vars, exec_write2_preserves_control_flow
 *
 *   Main preservation:
 *     step_effect_free_state_equiv — workhorse for simulation proofs
 *     step_nop_identity            — NOP is identity
 *     step_assert_identity         — ASSERT is identity on OK path
 *
 *   Write-opcode field preservation:
 *     step_mstore_preserves, step_sstore_preserves, step_tstore_preserves
 *     step_istore_preserves, step_log_preserves
 *     step_alloca_preserves
 *
 *   Write-effects soundness:
 *     write_effects_sound_storage, write_effects_sound_transient, ...
 *
 *   Context preservation (immutable fields):
 *     step_preserves_call_ctx, step_preserves_tx_ctx, step_preserves_block_ctx
 *     step_preserves_code, step_preserves_data_section, step_preserves_params
 *     step_preserves_label_offsets, step_preserves_prev_hashes
 *
 *   Non-output variable preservation:
 *     step_preserves_non_output_vars
 *)

Theory venomInstProofs
Ancestors
  venomExecSemantics venomEffects stateEquiv

(* ===================================================================== *)
(* ===== Section 1: Opcode Classification Properties ================== *)
(* ===================================================================== *)

(* Classification definitions (is_effect_free_op, is_mem_write_op,
   is_alloca_op, is_ext_call_op) are in venomInstScript.sml alongside
   is_terminator, is_volatile, is_pseudo. *)

(* Effect-free implies not a terminator *)
Theorem is_effect_free_not_terminator:
  !op. is_effect_free_op op ==> ~is_terminator op
Proof
  cheat
QED

(* ===================================================================== *)
(* ===== Section 2: Helper-Level Preservation ========================== *)
(* ===================================================================== *)

(* exec_pure1/2/3 produce state_equiv modulo output var *)

Theorem exec_pure1_state_equiv:
  !f inst s s'.
    exec_pure1 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  cheat
QED

Theorem exec_pure2_state_equiv:
  !f inst s s'.
    exec_pure2 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  cheat
QED

Theorem exec_pure3_state_equiv:
  !f inst s s'.
    exec_pure3 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  cheat
QED

(* exec_read0/1 produce state_equiv modulo output var *)

Theorem exec_read0_state_equiv:
  !f inst s s'.
    exec_read0 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  cheat
QED

Theorem exec_read1_state_equiv:
  !f inst s s'.
    exec_read1 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  cheat
QED

(* exec_write2 preserves variables when f preserves them.
   Applies to mstore, sstore, tstore (the actual use sites). *)

Theorem exec_write2_preserves_vars:
  !f inst s s'.
    exec_write2 f inst s = OK s' /\
    (!v1 v2 s0. (f v1 v2 s0).vs_vars = s0.vs_vars) ==>
    (!v. lookup_var v s' = lookup_var v s)
Proof
  cheat
QED

(* exec_write2 preserves control flow when f preserves it *)

Theorem exec_write2_preserves_control_flow:
  !f inst s s'.
    exec_write2 f inst s = OK s' /\
    (!v1 v2 s0. (f v1 v2 s0).vs_current_bb = s0.vs_current_bb /\
                (f v1 v2 s0).vs_inst_idx = s0.vs_inst_idx /\
                (f v1 v2 s0).vs_prev_bb = s0.vs_prev_bb) ==>
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  cheat
QED

(* ===================================================================== *)
(* ===== Section 3: Main Preservation Theorems ========================= *)
(* ===================================================================== *)

(* KEY LEMMA: Effect-free opcodes produce state_equiv modulo output vars.
   This is the main workhorse for simulation proofs. When replacing one
   effect-free instruction with another that produces the same value,
   the rest of the state is provably identical. *)
Theorem step_effect_free_state_equiv:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  cheat
QED

(* NOP is identity: produces OK with unchanged state *)
Theorem step_nop_identity:
  !fuel ctx inst s. inst.inst_opcode = NOP ==> step_inst fuel ctx inst s = OK s
Proof
  cheat
QED

(* ASSERT is identity on OK path *)
Theorem step_assert_identity:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = ASSERT ==>
    s' = s
Proof
  cheat
QED

(* ASSERT_UNREACHABLE is identity on OK path *)
Theorem step_assert_unreachable_identity:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode = ASSERT_UNREACHABLE ==>
    s' = s
Proof
  cheat
QED

(* ===================================================================== *)
(* ===== Section 4: Non-Output Variable Preservation =================== *)
(* ===================================================================== *)

(* For any non-terminator opcode that produces OK, variables not in
   inst_outputs are preserved. This covers ALL opcodes, not just
   effect-free ones — even MSTORE/SSTORE/LOG etc. preserve variables
   (they write state fields, not vars). *)
Theorem step_preserves_non_output_vars:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    !v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s
Proof
  cheat
QED

(* Corollary: exec_write2 opcodes (MSTORE, SSTORE, TSTORE) have no
   outputs, so ALL variables are preserved *)
Theorem step_write2_preserves_all_vars:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    (inst.inst_opcode = MSTORE \/ inst.inst_opcode = SSTORE \/
     inst.inst_opcode = TSTORE) ==>
    !v. lookup_var v s' = lookup_var v s
Proof
  cheat
QED

(* ===================================================================== *)
(* ===== Section 5: Write-Opcode Field Preservation ==================== *)
(* ===================================================================== *)

(* Each write opcode has a precise characterization of what it changes.
   These lemmas enumerate exactly which fields are preserved. *)

(* MSTORE: only changes vs_memory *)
Theorem step_mstore_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = MSTORE ==>
    s'.vs_transient = s.vs_transient /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  cheat
QED

(* SSTORE: only changes contract storage (in vs_accounts) *)
Theorem step_sstore_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = SSTORE ==>
    s'.vs_memory = s.vs_memory /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  cheat
QED

(* TSTORE: only changes vs_transient *)
Theorem step_tstore_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = TSTORE ==>
    s'.vs_memory = s.vs_memory /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  cheat
QED

(* ISTORE: only changes vs_immutables *)
Theorem step_istore_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = ISTORE ==>
    s'.vs_memory = s.vs_memory /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  cheat
QED

(* LOG: only changes vs_logs *)
Theorem step_log_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = LOG ==>
    s'.vs_memory = s.vs_memory /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  cheat
QED

(* Memory-writing opcodes: only change vs_memory (not storage/transient/etc) *)
Theorem step_mem_write_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ is_mem_write_op inst.inst_opcode ==>
    s'.vs_transient = s.vs_transient /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_label_offsets = s.vs_label_offsets /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  cheat
QED

(* ALLOCA/PALLOCA/CALLOCA: change vs_memory + vs_allocas + output var *)
Theorem step_alloca_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ is_alloca_op inst.inst_opcode ==>
    s'.vs_transient = s.vs_transient /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_label_offsets = s.vs_label_offsets /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s)
Proof
  cheat
QED

(* External calls: change accounts, storage, memory, returndata, logs,
   transient, and output var.
   Preserve: immutables, allocas, context fields, non-output vars.
   NOTE: vs_accounts and vs_transient are NOT preserved — reentrancy
   allows the callee to call back and execute SSTORE/TSTORE at the
   caller's address.  DELEGATECALL does this directly (callee runs
   at caller's address). *)
Theorem step_ext_call_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ is_ext_call_op inst.inst_opcode ==>
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_label_offsets = s.vs_label_offsets /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s)
Proof
  cheat
QED



(* ===================================================================== *)
(* ===== Section 6: Write-Effects Soundness ============================ *)
(* ===================================================================== *)

(* These link the effects system (write_effects) to actual semantics.
   Each theorem: if the declared write_effects don't include effect X,
   then state field Y is preserved.
   Excludes allocation opcodes (ALLOCA/PALLOCA/CALLOCA) which are not
   tracked by the effects system (they're IR-level, not EVM). *)

Theorem write_effects_sound_storage:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    contract_storage s' = contract_storage s
Proof
  cheat
QED

Theorem write_effects_sound_transient:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
    s'.vs_transient = s.vs_transient
Proof
  cheat
QED

(* Eff_MSIZE is NOT required: in our model, opcodes with Eff_MSIZE but
   not Eff_MEMORY (MLOAD, SHA3, LOG, ILOAD, CREATE/CREATE2) do not
   actually modify vs_memory. EVM memory expansion is not modeled. *)
Theorem write_effects_sound_memory:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
    s'.vs_memory = s.vs_memory
Proof
  cheat
QED

Theorem write_effects_sound_immutables:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_IMMUTABLES NOTIN write_effects inst.inst_opcode ==>
    s'.vs_immutables = s.vs_immutables
Proof
  cheat
QED

Theorem write_effects_sound_returndata:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_RETURNDATA NOTIN write_effects inst.inst_opcode ==>
    s'.vs_returndata = s.vs_returndata
Proof
  cheat
QED

Theorem write_effects_sound_log:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_LOG NOTIN write_effects inst.inst_opcode ==>
    s'.vs_logs = s.vs_logs
Proof
  cheat
QED

(* vs_accounts is preserved when neither balance nor storage effects
   are present. SSTORE writes contract storage through vs_accounts,
   so Eff_STORAGE alone can change vs_accounts. *)
Theorem write_effects_sound_accounts:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    s'.vs_accounts = s.vs_accounts
Proof
  cheat
QED

(* ===================================================================== *)
(* ===== Section 7: Context Field Preservation ========================= *)
(* ===================================================================== *)

(* These "immutable context" fields are never modified by any non-terminator
   opcode. They are set at call entry and remain constant throughout
   intra-function execution. *)

Theorem step_preserves_call_ctx:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_call_ctx = s.vs_call_ctx
Proof
  cheat
QED

Theorem step_preserves_tx_ctx:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_tx_ctx = s.vs_tx_ctx
Proof
  cheat
QED

Theorem step_preserves_block_ctx:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  cheat
QED

Theorem step_preserves_code:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_code = s.vs_code
Proof
  cheat
QED

Theorem step_preserves_data_section:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_data_section = s.vs_data_section
Proof
  cheat
QED

Theorem step_preserves_label_offsets:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_label_offsets = s.vs_label_offsets
Proof
  cheat
QED

Theorem step_preserves_params:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_params = s.vs_params
Proof
  cheat
QED

Theorem step_preserves_prev_hashes:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_prev_hashes = s.vs_prev_hashes
Proof
  cheat
QED

(* Halted flag is never set by non-terminator opcodes *)
Theorem step_preserves_halted:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_halted = s.vs_halted
Proof
  cheat
QED

(* Control flow fields preserved by non-terminator opcodes *)
Theorem step_preserves_control_flow:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  cheat
QED

(* ===================================================================== *)
(* ===== Section 8: Derived Equivalences =============================== *)
(* ===================================================================== *)

(* Effect-free opcodes also give execution_equiv (weaker, for terminals) *)
Theorem step_effect_free_execution_equiv:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    execution_equiv (set inst.inst_outputs) s s'
Proof
  cheat
QED

(* Combining effect-free with same-value output gives full state_equiv {} *)
Theorem step_effect_free_same_value:
  !fuel ctx inst1 inst2 s s1 s2.
    step_inst fuel ctx inst1 s = OK s1 /\
    step_inst fuel ctx inst2 s = OK s2 /\
    is_effect_free_op inst1.inst_opcode /\
    is_effect_free_op inst2.inst_opcode /\
    inst1.inst_outputs = inst2.inst_outputs /\
    (* Both produce the same output value *)
    (!v. MEM v inst1.inst_outputs ==>
         lookup_var v s1 = lookup_var v s2) ==>
    state_equiv {} s1 s2
Proof
  cheat
QED
