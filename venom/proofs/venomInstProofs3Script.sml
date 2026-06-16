(*
 * Per-Opcode State Preservation Lemmas (Part 3: Static Field Proofs 2)
 *
 * Accounts and memory field preservation. These proofs each do a
 * full 94-opcode case split (heavy compilation).
 *
 * Split from venomInstProofsScript.sml for build timeout reasons.
 *)

Theory venomInstProofs3
Ancestors
  finite_map pred_set
  venomState venomExecSemantics venomInst venomEffects
  stateEquivProofs
  venomInstProofs1 venomInstProofs2

Theorem exec_pure1_memory_preserves:
  exec_pure1 x y s = OK s' ==> s'.vs_memory = s.vs_memory
Proof
  rw[exec_pure1_def, AllCaseEqs(), update_var_def] >> gvs[]
QED

Theorem exec_read0_memory_preserves:
  exec_read0 x y s = OK s' ==> s'.vs_memory = s.vs_memory
Proof
  rw[exec_read0_def, AllCaseEqs(), update_var_def] >> gvs[]
QED

Theorem exec_read1_memory_preserves:
  exec_read1 x y s = OK s' ==> s'.vs_memory = s.vs_memory
Proof
  rw[exec_read1_def, AllCaseEqs(), update_var_def] >> gvs[]
QED

Theorem exec_pure2_memory_preserves:
  exec_pure2 x y s = OK s' ==> s'.vs_memory = s.vs_memory
Proof
  rw[exec_pure2_def, AllCaseEqs(), update_var_def] >> gvs[]
QED

Theorem exec_pure3_memory_preserves:
  exec_pure3 x y s = OK s' ==> s'.vs_memory = s.vs_memory
Proof
  rw[exec_pure3_def, AllCaseEqs(), update_var_def] >> gvs[]
QED

Theorem step_inst_base_preserves_account_memory_fields:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode ==>
    (Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
     Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
     s'.vs_accounts = s.vs_accounts) /\
    (Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
     s'.vs_memory = s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[step_inst_base_def, AllCaseEqs(),
      is_terminator_def, is_alloca_op_def,
      write_effects_def, empty_effects_def,
      update_var_def] >>
  imp_res_tac exec_pure1_static_preserves >>
  imp_res_tac exec_read0_static_preserves >>
  imp_res_tac exec_read1_static_preserves >>
  imp_res_tac exec_pure2_static_preserves >>
  imp_res_tac exec_ext_call_static_preserves >>
  imp_res_tac exec_pure3_static_preserves >>
  imp_res_tac exec_pure1_memory_preserves >>
  imp_res_tac exec_read0_memory_preserves >>
  imp_res_tac exec_read1_memory_preserves >>
  imp_res_tac exec_pure2_memory_preserves >>
  imp_res_tac exec_pure3_memory_preserves >> gvs[] >>
  gvs[exec_write2_def, exec_create_def, AllCaseEqs(),
      extract_venom_result_def,
      mcopy_def, mstore_def, mstore8_def,
      write_memory_with_expansion_def,
      sstore_def, tstore_def, all_effects_def,
      update_var_def] >> gvs[] >>
  Cases_on `result` >> gvs[] >>
  Cases_on `y` >> gvs[]
QED

Theorem step_inst_base_preserves_accounts:
  (* A non-terminating, non-alloca instruction with no BALANCE or STORAGE
     write effects preserves the accounts field of the state. *)
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    s'.vs_accounts = s.vs_accounts
Proof
  metis_tac[step_inst_base_preserves_account_memory_fields]
QED

Theorem step_inst_base_preserves_memory:
  (* A non-terminating, non-alloca instruction with no MEMORY write effect
     preserves the memory field of the state. *)
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
    s'.vs_memory = s.vs_memory
Proof
  metis_tac[step_inst_base_preserves_account_memory_fields]
QED
