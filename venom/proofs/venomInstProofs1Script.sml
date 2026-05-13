(*
 * Per-Opcode State Preservation Lemmas (Part 1: Core)
 *
 * Opcode classification, helper preservation, main preservation,
 * write-opcode field preservation, and mega-lemma infrastructure.
 *
 * Split from venomInstProofsScript.sml for build timeout reasons.
 *)

Theory venomInstProofs1
Ancestors
  venomExecSemantics venomEffects stateEquiv stateEquivProofs
  vfmStaticCalls finite_map venomState venomInst pred_set

(* ===================================================================== *)
(* ===== Section 1: Opcode Classification Properties ================== *)
(* ===================================================================== *)

Theorem is_effect_free_not_terminator:
  !op. is_effect_free_op op ==> ~is_terminator op
Proof
  Cases >> EVAL_TAC
QED

(* ===================================================================== *)
(* ===== Section 2: Helper-Level Preservation ========================== *)
(* ===================================================================== *)

Theorem update_var_state_equiv:
  !out v s. state_equiv {out} s (update_var out v s)
Proof
  rw[state_equiv_def, execution_equiv_def,
     update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

val exec_state_equiv_tac =
  gvs[AllCaseEqs()] >>
  irule state_equiv_subset >>
  qexists_tac `{out}` >>
  simp[update_var_state_equiv, SUBSET_DEF];

Theorem exec_pure1_state_equiv:
  !f inst s s'.
    exec_pure1 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rw[exec_pure1_def] >> exec_state_equiv_tac
QED

Theorem exec_pure2_state_equiv:
  !f inst s s'.
    exec_pure2 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rw[exec_pure2_def] >> exec_state_equiv_tac
QED

Theorem exec_pure3_state_equiv:
  !f inst s s'.
    exec_pure3 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rw[exec_pure3_def] >> exec_state_equiv_tac
QED

Theorem exec_read0_state_equiv:
  !f inst s s'.
    exec_read0 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rw[exec_read0_def] >> exec_state_equiv_tac
QED

Theorem exec_read1_state_equiv:
  !f inst s s'.
    exec_read1 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rw[exec_read1_def] >> exec_state_equiv_tac
QED

val exec_write2_tac =
  rw[exec_write2_def, AllCaseEqs()] >> gvs[];

Theorem exec_write2_preserves_vars:
  !f inst s s'.
    exec_write2 f inst s = OK s' /\
    (!v1 v2 s0. (f v1 v2 s0).vs_vars = s0.vs_vars) ==>
    (!v. lookup_var v s' = lookup_var v s)
Proof
  exec_write2_tac >> rw[lookup_var_def]
QED

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
  exec_write2_tac
QED

(* ===================================================================== *)
(* ===== Section 3: Main Preservation Theorems ========================= *)
(* ===================================================================== *)

(* NOP is identity: produces OK with unchanged state *)
val reduce_to_base_tac =
  rw[Once step_inst_def] >> simp[step_inst_base_def];

Theorem step_nop_identity:
  !fuel ctx inst s. inst.inst_opcode = NOP ==> step_inst fuel ctx inst s = OK s
Proof
  reduce_to_base_tac
QED

Theorem step_assert_identity:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = ASSERT ==>
    s' = s
Proof
  rw[Once step_inst_def, step_inst_base_def] >> gvs[AllCaseEqs()]
QED

Theorem step_assert_unreachable_identity:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode = ASSERT_UNREACHABLE ==>
    s' = s
Proof
  rw[Once step_inst_def, step_inst_base_def] >> gvs[AllCaseEqs()]
QED

(* ===================================================================== *)
(* ===== Section 5: Write-Opcode Field Preservation ==================== *)
(* ===================================================================== *)

val write_finish_tac =
  gvs[AllCaseEqs(), exec_write2_def, exec_alloca_def, exec_ext_call_def,
      exec_delegatecall_def, exec_create_def,
      extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  simp[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
       write_memory_with_expansion_def, mcopy_def,
       contract_storage_def, revert_state_def,
       lookup_var_def, FLOOKUP_UPDATE, eval_operands_def];

val step_specific_write_tac =
  rw[Once step_inst_def, step_inst_base_def] >>
  gvs[AllCaseEqs()] >> write_finish_tac;

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
  step_specific_write_tac
QED

Theorem step_mstore8_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = MSTORE8 ==>
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
  step_specific_write_tac
QED

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
  step_specific_write_tac
QED

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
  step_specific_write_tac
QED

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
  step_specific_write_tac
QED

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
  step_specific_write_tac
QED

(* ===================================================================== *)
(* ===== Mega-Lemma Infrastructure ===================================== *)
(* ===================================================================== *)

(* FOLDL of update_var preserves any field that update_var preserves *)
Theorem foldl_update_var_preserves:
  !f. (!k v s. f (update_var k v s) = f s) ==>
      !kvs s. f (FOLDL (\s' (k,v). update_var k v s') s kvs) = f s
Proof
  strip_tac >> strip_tac >> Induct >>
  simp[pairTheory.FORALL_PROD]
QED

(* bind_outputs preserves any field that update_var preserves *)
Theorem bind_outputs_preserves:
  !f. (!k v s. f (update_var k v s) = f s) ==>
      !outs vals s s'. bind_outputs outs vals s = SOME s' ==> f s' = f s
Proof
  rw[bind_outputs_def] >> gvs[] >> metis_tac[foldl_update_var_preserves]
QED

(* Tactic: prove step_inst_base preserves a field for non-terminators.
   Includes write_effects/is_alloca_op for conditional preservation. *)
val step_base_field_tac =
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs(), is_terminator_def,
      write_effects_def, all_effects_def, empty_effects_def,
      is_alloca_op_def] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_ext_call_def, exec_delegatecall_def,
     exec_create_def, exec_alloca_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
     write_memory_with_expansion_def, mcopy_def,
     revert_state_def, eval_operands_def,
     lookup_var_def, FLOOKUP_UPDATE];

(* Single mega-lemma: all fields preserved by step_inst_base for
   non-terminators. One 94-opcode case split. *)
Theorem step_inst_base_preserves_all:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s) /\
    (~is_alloca_op inst.inst_opcode /\
     Eff_IMMUTABLES NOTIN write_effects inst.inst_opcode ==>
     s'.vs_immutables = s.vs_immutables) /\
    (~is_alloca_op inst.inst_opcode /\
     Eff_RETURNDATA NOTIN write_effects inst.inst_opcode ==>
     s'.vs_returndata = s.vs_returndata)
Proof
  step_base_field_tac
QED

(* Generic lift: from step_inst_base mega-lemma to step_inst for any field *)
fun step_inst_lift_from_all_tac field_fn =
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  (gvs[bind_outputs_def, merge_callee_state_def] >>
   qspecl_then [field_fn] mp_tac foldl_update_var_preserves >>
   simp[update_var_def]) >>
  imp_res_tac step_inst_base_preserves_all >> gvs[is_terminator_def];
