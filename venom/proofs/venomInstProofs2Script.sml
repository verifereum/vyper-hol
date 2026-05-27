(*
 * Per-Opcode State Preservation Lemmas (Part 2: Static Field Proofs 1)
 *
 * EVM static-mode invariant and storage/transient/log field preservation.
 * These proofs each do a full 94-opcode case split (heavy compilation).
 *
 * Split from venomInstProofsScript.sml for build timeout reasons.
 *)

Theory venomInstProofs2
Ancestors
  venomInstProofs1 stateEquivProofs finite_map venomState
  venomExecSemantics venomInst venomEffects pred_set

(* ===================================================================== *)
(* ===== EVM Static-Mode Invariant (upstream dependency) =============== *)
(* ===================================================================== *)

(* A static external call (STATICCALL) preserves accounts, transient
   storage, logs, and call context — value=0 and static mode mean no
   state mutation escapes the call. *)
Theorem exec_ext_call_static_preserves:
  !inst s gas addr_w argsOff argsSize retOff retSize s'.
    exec_ext_call inst s gas addr_w (0w:bytes32) argsOff argsSize
                  retOff retSize T = OK s' ==>
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_call_ctx = s.vs_call_ctx
Proof
  rw[exec_ext_call_def, make_venom_call_state_def, LET_DEF] >>
  gvs[AllCaseEqs()] >>
  simp[update_var_def] >>
  fs[extract_venom_result_def] >> gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  Cases_on `result` >> gvs[] >>
  Cases_on `y` >> gvs[] >>
  drule vfmStaticCallsTheory.run_static_preserves >>
  simp[vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def,
       vfmContextTheory.empty_return_destination_def,
       make_rollback_def, vfmExecutionTheory.transfer_value_def] >>
  strip_tac >> gvs[]
QED

(* For non-terminator, non-alloca opcodes without the corresponding
   write effect, step_inst_base preserves storage / transient storage /
   log fields. STATICCALL is the only such opcode that touches these
   fields, and static mode ensures preservation. *)

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

Theorem step_inst_base_preserves_storage:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    contract_storage s' = contract_storage s
Proof
  step_base_static_field_tac
QED

Theorem step_inst_base_preserves_transient:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
    s'.vs_transient = s.vs_transient
Proof
  step_base_static_field_tac
QED

Theorem step_inst_base_preserves_log:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    Eff_LOG NOTIN write_effects inst.inst_opcode ==>
    s'.vs_logs = s.vs_logs
Proof
  step_base_static_field_tac
QED
