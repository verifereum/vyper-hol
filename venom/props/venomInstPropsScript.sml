(*
 * Per-Opcode State Preservation Properties (ACCEPT_TAC wrappers)
 *
 * Re-exports theorems from venomInstProofs.
 * Definitions (is_effect_free_op etc.) available via ancestor chain.
 *
 * See venomInstProofsScript.sml for full documentation.
 *)

Theory venomInstProps
Ancestors
  venomInstProofs

Theorem is_effect_free_not_terminator:!op. is_effect_free_op op ==> ~is_terminator op
Proof
  ACCEPT_TAC venomInstProofsTheory.is_effect_free_not_terminator
QED

Theorem exec_pure1_state_equiv:!f inst s s'.
    exec_pure1 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  ACCEPT_TAC venomInstProofsTheory.exec_pure1_state_equiv
QED

Theorem exec_pure2_state_equiv:!f inst s s'.
    exec_pure2 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  ACCEPT_TAC venomInstProofsTheory.exec_pure2_state_equiv
QED

Theorem exec_pure3_state_equiv:!f inst s s'.
    exec_pure3 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  ACCEPT_TAC venomInstProofsTheory.exec_pure3_state_equiv
QED

Theorem exec_read0_state_equiv:!f inst s s'.
    exec_read0 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  ACCEPT_TAC venomInstProofsTheory.exec_read0_state_equiv
QED

Theorem exec_read1_state_equiv:!f inst s s'.
    exec_read1 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  ACCEPT_TAC venomInstProofsTheory.exec_read1_state_equiv
QED

Theorem exec_write2_preserves_vars:!f inst s s'.
    exec_write2 f inst s = OK s' /\
    (!v1 v2 s0. (f v1 v2 s0).vs_vars = s0.vs_vars) ==>
    (!v. lookup_var v s' = lookup_var v s)
Proof
  ACCEPT_TAC venomInstProofsTheory.exec_write2_preserves_vars
QED

Theorem exec_write2_preserves_control_flow:!f inst s s'.
    exec_write2 f inst s = OK s' /\
    (!v1 v2 s0. (f v1 v2 s0).vs_current_bb = s0.vs_current_bb /\
                (f v1 v2 s0).vs_inst_idx = s0.vs_inst_idx /\
                (f v1 v2 s0).vs_prev_bb = s0.vs_prev_bb) ==>
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  ACCEPT_TAC venomInstProofsTheory.exec_write2_preserves_control_flow
QED

Theorem step_effect_free_state_equiv:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  ACCEPT_TAC venomInstProofsTheory.step_effect_free_state_equiv
QED

Theorem step_nop_identity:!fuel ctx inst s. inst.inst_opcode = NOP ==> step_inst fuel ctx inst s = OK s
Proof
  ACCEPT_TAC venomInstProofsTheory.step_nop_identity
QED

Theorem step_assert_identity:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = ASSERT ==>
    s' = s
Proof
  ACCEPT_TAC venomInstProofsTheory.step_assert_identity
QED

Theorem step_assert_unreachable_identity:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode = ASSERT_UNREACHABLE ==>
    s' = s
Proof
  ACCEPT_TAC venomInstProofsTheory.step_assert_unreachable_identity
QED

Theorem step_preserves_non_output_vars:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    !v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s
Proof
  ACCEPT_TAC venomInstProofsTheory.step_preserves_non_output_vars
QED

Theorem step_write2_preserves_all_vars:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    (inst.inst_opcode = MSTORE \/ inst.inst_opcode = SSTORE \/
     inst.inst_opcode = TSTORE) ==>
    !v. lookup_var v s' = lookup_var v s
Proof
  ACCEPT_TAC venomInstProofsTheory.step_write2_preserves_all_vars
QED

Theorem step_mstore_preserves:!fuel ctx inst s s'.
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
  ACCEPT_TAC venomInstProofsTheory.step_mstore_preserves
QED

Theorem step_sstore_preserves:!fuel ctx inst s s'.
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
  ACCEPT_TAC venomInstProofsTheory.step_sstore_preserves
QED

Theorem step_tstore_preserves:!fuel ctx inst s s'.
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
  ACCEPT_TAC venomInstProofsTheory.step_tstore_preserves
QED

Theorem step_istore_preserves:!fuel ctx inst s s'.
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
  ACCEPT_TAC venomInstProofsTheory.step_istore_preserves
QED

Theorem step_log_preserves:!fuel ctx inst s s'.
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
  ACCEPT_TAC venomInstProofsTheory.step_log_preserves
QED

Theorem step_mem_write_preserves:!fuel ctx inst s s'.
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
  ACCEPT_TAC venomInstProofsTheory.step_mem_write_preserves
QED

Theorem step_alloca_preserves:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ is_alloca_op inst.inst_opcode ==>
    s'.vs_memory = s.vs_memory /\
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
  ACCEPT_TAC venomInstProofsTheory.step_alloca_preserves
QED

Theorem step_ext_call_preserves:!fuel ctx inst s s'.
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
  ACCEPT_TAC venomInstProofsTheory.step_ext_call_preserves
QED


Theorem write_effects_sound_storage:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    contract_storage s' = contract_storage s
Proof
  ACCEPT_TAC venomInstProofsTheory.write_effects_sound_storage
QED

Theorem write_effects_sound_transient:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
    s'.vs_transient = s.vs_transient
Proof
  ACCEPT_TAC venomInstProofsTheory.write_effects_sound_transient
QED

Theorem write_effects_sound_memory:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
    s'.vs_memory = s.vs_memory
Proof
  ACCEPT_TAC venomInstProofsTheory.write_effects_sound_memory
QED

Theorem write_effects_sound_immutables:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_IMMUTABLES NOTIN write_effects inst.inst_opcode ==>
    s'.vs_immutables = s.vs_immutables
Proof
  ACCEPT_TAC venomInstProofsTheory.write_effects_sound_immutables
QED

Theorem write_effects_sound_returndata:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_RETURNDATA NOTIN write_effects inst.inst_opcode ==>
    s'.vs_returndata = s.vs_returndata
Proof
  ACCEPT_TAC venomInstProofsTheory.write_effects_sound_returndata
QED

Theorem write_effects_sound_log:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_LOG NOTIN write_effects inst.inst_opcode ==>
    s'.vs_logs = s.vs_logs
Proof
  ACCEPT_TAC venomInstProofsTheory.write_effects_sound_log
QED

Theorem write_effects_sound_accounts:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    s'.vs_accounts = s.vs_accounts
Proof
  ACCEPT_TAC venomInstProofsTheory.write_effects_sound_accounts
QED

Theorem step_preserves_call_ctx:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_call_ctx = s.vs_call_ctx
Proof
  ACCEPT_TAC venomInstProofsTheory.step_preserves_call_ctx
QED

Theorem step_preserves_tx_ctx:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_tx_ctx = s.vs_tx_ctx
Proof
  ACCEPT_TAC venomInstProofsTheory.step_preserves_tx_ctx
QED

Theorem step_preserves_block_ctx:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  ACCEPT_TAC venomInstProofsTheory.step_preserves_block_ctx
QED

Theorem step_preserves_code:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_code = s.vs_code
Proof
  ACCEPT_TAC venomInstProofsTheory.step_preserves_code
QED

Theorem step_preserves_data_section:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_data_section = s.vs_data_section
Proof
  ACCEPT_TAC venomInstProofsTheory.step_preserves_data_section
QED

Theorem step_preserves_label_offsets:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_label_offsets = s.vs_label_offsets
Proof
  ACCEPT_TAC venomInstProofsTheory.step_preserves_label_offsets
QED

Theorem step_preserves_params:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_params = s.vs_params
Proof
  ACCEPT_TAC venomInstProofsTheory.step_preserves_params
QED

Theorem step_preserves_prev_hashes:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_prev_hashes = s.vs_prev_hashes
Proof
  ACCEPT_TAC venomInstProofsTheory.step_preserves_prev_hashes
QED

Theorem step_preserves_halted:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_halted = s.vs_halted
Proof
  ACCEPT_TAC venomInstProofsTheory.step_preserves_halted
QED

Theorem step_preserves_control_flow:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  ACCEPT_TAC venomInstProofsTheory.step_preserves_control_flow
QED

Theorem step_effect_free_execution_equiv:!fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    execution_equiv (set inst.inst_outputs) s s'
Proof
  ACCEPT_TAC venomInstProofsTheory.step_effect_free_execution_equiv
QED

Theorem step_effect_free_same_value:!fuel ctx inst1 inst2 s s1 s2.
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
  ACCEPT_TAC venomInstProofsTheory.step_effect_free_same_value
QED

