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

val step_base_static_field_tac =
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def,
      write_effects_def, all_effects_def, empty_effects_def] >>
  fs[step_inst_base_def] >>
  gvs[AllCaseEqs()] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_create_def, extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  simp[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
       write_memory_with_expansion_def, mcopy_def,
       contract_storage_def] >>
  imp_res_tac exec_ext_call_static_preserves >> gvs[];

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
  step_base_static_field_tac
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
  step_base_static_field_tac
QED
