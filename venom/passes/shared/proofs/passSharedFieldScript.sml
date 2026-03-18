(*
 * Field preservation for non-ext-call instructions.
 *)

Theory passSharedField
Ancestors
  passSharedDefs venomExecSemantics venomEffects venomInstProps

open venomStateTheory venomInstTheory venomExecSemanticsTheory
     venomEffectsTheory passSharedDefsTheory venomInstPropsTheory;

(* Upstream-style tactic *)
val field_tac =
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs(), is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, all_effects_def, empty_effects_def] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_alloca_def, extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, mstore_def, sstore_def, tstore_def,
     write_memory_with_expansion_def, mcopy_def,
     contract_storage_def, contract_transient_def];

Theorem step_base_preserves_transient[local]:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
    s'.vs_transient = s.vs_transient
Proof
  field_tac
QED

Theorem step_base_preserves_accounts[local]:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    s'.vs_accounts = s.vs_accounts
Proof
  field_tac
QED

Theorem step_base_preserves_logs[local]:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_LOG NOTIN write_effects inst.inst_opcode ==>
    s'.vs_logs = s.vs_logs
Proof
  field_tac
QED

Theorem step_base_preserves_tracked:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode ==>
    (Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
      s'.vs_transient = s.vs_transient) /\
    (Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
     Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
      s'.vs_accounts = s.vs_accounts) /\
    (Eff_LOG NOTIN write_effects inst.inst_opcode ==>
      s'.vs_logs = s.vs_logs)
Proof
  metis_tac[step_base_preserves_transient,
            step_base_preserves_accounts,
            step_base_preserves_logs]
QED

(* Combined preservation theorem: all field preservation facts in one.
   Use with targeted qpat_x_assum to avoid metis search with multiple
   step_inst assumptions. *)
Theorem step_inst_preserves_all:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    (* Always preserved (Group A) *)
    s'.vs_prev_bb = s.vs_prev_bb /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_label_offsets = s.vs_label_offsets /\
    s'.vs_code = s.vs_code /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    (* Conditionally preserved (Group B) *)
    (Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
      s'.vs_memory = s.vs_memory) /\
    (Eff_IMMUTABLES NOTIN write_effects inst.inst_opcode ==>
      s'.vs_immutables = s.vs_immutables) /\
    (Eff_RETURNDATA NOTIN write_effects inst.inst_opcode ==>
      s'.vs_returndata = s.vs_returndata) /\
    (Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
      s'.vs_transient = s.vs_transient) /\
    (Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
     Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
      s'.vs_accounts = s.vs_accounts) /\
    (Eff_LOG NOTIN write_effects inst.inst_opcode ==>
      s'.vs_logs = s.vs_logs)
Proof
  rpt strip_tac >>
  `step_inst_base inst s = OK s'` by gvs[step_inst_non_invoke] >>
  metis_tac[step_preserves_control_flow, step_preserves_halted,
            step_preserves_call_ctx, step_preserves_tx_ctx,
            step_preserves_block_ctx, step_preserves_data_section,
            step_preserves_label_offsets, step_preserves_code,
            step_preserves_params, step_preserves_prev_hashes,
            write_effects_sound_memory, write_effects_sound_immutables,
            write_effects_sound_returndata,
            step_base_preserves_tracked]
QED

(* No eligible opcode writes Eff_BALANCE or Eff_EXTCODE.
   These effects only appear in write_effects of ext_call ops
   (CALL, STATICCALL, DELEGATECALL, CREATE, CREATE2) and SELFDESTRUCT
   (a terminator). This is critical for the accounts field in
   output_determined: preserves_all for accounts needs BOTH
   Eff_BALANCE and Eff_STORAGE to not be in write_effects. *)
Theorem eligible_no_write_balance_extcode:
  !op. ~is_terminator op /\ ~is_alloca_op op /\
       ~is_ext_call_op op /\ op <> INVOKE ==>
       Eff_BALANCE NOTIN write_effects op /\
       Eff_EXTCODE NOTIN write_effects op
Proof
  Cases >> simp[is_terminator_def, is_alloca_op_def,
                is_ext_call_op_def, write_effects_def,
                all_effects_def, empty_effects_def]
QED

val _ = export_theory();
