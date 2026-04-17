(*
 * Field preservation for non-ext-call instructions.
 *)

Theory passSharedField
Ancestors
  passSharedDefs venomExecSemantics venomEffects venomInstProps
  venomState venomInst

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
  fs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
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
    s'.vs_labels = s.vs_labels /\
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
            step_preserves_code, step_preserves_labels,
            step_preserves_params, step_preserves_prev_hashes,
            write_effects_sound_memory, write_effects_sound_immutables,
            write_effects_sound_returndata,
            step_base_preserves_tracked]
QED

(* ----------------------------------------------------------------
   Memory Frame Lemma
   
   Non-volatile-memory instructions produce the same result when
   vs_memory is replaced.  "Non-volatile-memory" means no Eff_MEMORY
   in read_effects or write_effects.
   
   Why: eval_operand only reads vs_vars, update_var only writes
   vs_vars, and the state-reader functions for non-memory opcodes
   (sload, tload, calldataload, dload, etc.) don't access vs_memory.
   ---------------------------------------------------------------- *)

(* Building blocks *)
Theorem eval_operand_mem[local,simp]:
  !op s m. eval_operand op (s with vs_memory := m) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_operands_mem[local,simp]:
  !ops s m. eval_operands ops (s with vs_memory := m) = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def] >>
  rw[] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED

Theorem update_var_mem[local,simp]:
  !x v s m. update_var x v (s with vs_memory := m) =
             (update_var x v s) with vs_memory := m
Proof
  simp[update_var_def]
QED

(* State-access functions: memory independence.
   Read-only functions return the same value when vs_memory changes.
   Write functions commute with vs_memory update. *)
Theorem sload_mem[local,simp]:
  !key (s:venom_state) m. sload key (s with vs_memory := m) = sload key s
Proof
  simp[sload_def, contract_storage_def]
QED

Theorem tload_mem[local,simp]:
  !key (s:venom_state) m. tload key (s with vs_memory := m) = tload key s
Proof
  simp[tload_def, contract_transient_def]
QED

Theorem sstore_mem[local,simp]:
  !key val (s:venom_state) m.
    sstore key val (s with vs_memory := m) =
    (sstore key val s) with vs_memory := m
Proof
  simp[sstore_def, LET_THM, vfmStateTheory.lookup_account_def]
QED

Theorem tstore_mem[local,simp]:
  !key val (s:venom_state) m.
    tstore key val (s with vs_memory := m) =
    (tstore key val s) with vs_memory := m
Proof
  simp[tstore_def, LET_THM, contract_transient_def]
QED

(* Frame tactic: like field_tac but rewrites eval_operand/update_var
   plus state-access functions that don't depend on vs_memory *)
val mem_frame_tac =
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs(), is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, read_effects_def, all_effects_def, empty_effects_def] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_alloca_def, extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, vfmStateTheory.lookup_account_def];

Theorem step_inst_base_mem_frame[local]:
  !inst s s' m.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode
    ==>
    step_inst_base inst (s with vs_memory := m) =
    OK (s' with vs_memory := m)
Proof
  mem_frame_tac
QED

(* Lift to step_inst (adds INVOKE + ALLOCA exclusions).
   ALLOCA uses vs_alloca_next as bump pointer;
   it does not read LENGTH vs_memory. *)
Theorem step_inst_mem_frame:
  !fuel ctx inst s s' m.
    step_inst fuel ctx inst s = OK s' /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE
    ==>
    step_inst fuel ctx inst (s with vs_memory := m) =
    OK (s' with vs_memory := m)
Proof
  rpt strip_tac >>
  `step_inst_base inst s = OK s'` by gvs[step_inst_non_invoke] >>
  `step_inst_base inst (s with vs_memory := m) =
   OK (s' with vs_memory := m)` by metis_tac[step_inst_base_mem_frame] >>
  gvs[step_inst_non_invoke]
QED

(* Error case: same error regardless of memory replacement *)
Theorem step_inst_base_mem_error_frame[local]:
  !inst s e m.
    step_inst_base inst s = Error e /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode
    ==>
    step_inst_base inst (s with vs_memory := m) = Error e
Proof
  mem_frame_tac
QED

Theorem step_inst_mem_error_frame:
  !fuel ctx inst s e m.
    step_inst fuel ctx inst s = Error e /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE
    ==>
    step_inst fuel ctx inst (s with vs_memory := m) = Error e
Proof
  rpt strip_tac >>
  `step_inst_base inst s = Error e` by gvs[step_inst_non_invoke] >>
  `step_inst_base inst (s with vs_memory := m) = Error e`
    by metis_tac[step_inst_base_mem_error_frame] >>
  gvs[step_inst_non_invoke]
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
