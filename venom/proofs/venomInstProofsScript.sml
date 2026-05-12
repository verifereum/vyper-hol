(*
 * Per-Opcode State Preservation Lemmas
 *
 * Classifies opcodes by their effect on state and provides preservation
 * lemmas for pass correctness proofs.
 *)

Theory venomInstProofs
Ancestors
  venomExecSemantics venomEffects stateEquiv stateEquivProofs
  vfmStaticCalls

open stateEquivProofsTheory
open finite_mapTheory
open venomStateTheory venomExecSemanticsTheory venomInstTheory
open venomEffectsTheory pred_setTheory

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

Theorem update_var_state_equiv[local]:
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

Triviality state_equiv_step_base_concl:
  !inst s s'.
    state_equiv (set inst.inst_outputs) s s' ==>
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
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata
Proof
  rw[state_equiv_def, execution_equiv_def] >>
  first_x_assum drule >> simp[]
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

(* step_effect_free_state_equiv: proved after mega-lemma is available. *)

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
  rw[Once step_inst_def] >>
  gvs[] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  write_finish_tac;

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
  rpt gen_tac >> strip_tac >>
  fs[Once step_inst_def] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  write_finish_tac
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
  rpt gen_tac >> strip_tac >>
  fs[Once step_inst_def] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  write_finish_tac
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
  rpt gen_tac >> strip_tac >>
  fs[Once step_inst_def] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  write_finish_tac
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
  rpt gen_tac >> strip_tac >>
  fs[Once step_inst_def] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  write_finish_tac
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
  rpt gen_tac >> strip_tac >>
  fs[Once step_inst_def] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  write_finish_tac
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
  rpt gen_tac >> strip_tac >>
  fs[Once step_inst_def] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  write_finish_tac
QED

(* ===================================================================== *)
(* ===== Mega-Lemma Infrastructure ===================================== *)
(* ===================================================================== *)

(* FOLDL of update_var preserves any field that update_var preserves *)
Theorem foldl_update_var_preserves[local]:
  !f. (!k v s. f (update_var k v s) = f s) ==>
      !kvs s. f (FOLDL (\s' (k,v). update_var k v s') s kvs) = f s
Proof
  strip_tac >> strip_tac >> Induct >>
  simp[pairTheory.FORALL_PROD]
QED

(* bind_outputs preserves any field that update_var preserves *)
Theorem bind_outputs_preserves[local]:
  !f. (!k v s. f (update_var k v s) = f s) ==>
      !outs vals s s'. bind_outputs outs vals s = SOME s' ==> f s' = f s
Proof
  rw[bind_outputs_def] >> gvs[] >> metis_tac[foldl_update_var_preserves]
QED

(* Tactic: prove step_inst_base preserves a field for non-terminators.
   Includes write_effects/is_alloca_op for conditional preservation. *)
val step_base_field_finish_tac =
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

val step_base_field_tac =
  rw[step_inst_base_def] >> step_base_field_finish_tac;

Triviality nonterminator_opcode_class:
  !op. ~is_terminator op ==>
    is_effect_free_op op \/
    is_mem_write_op op \/
    is_alloca_op op \/
    is_ext_call_op op \/
    op = SSTORE \/ op = TSTORE \/ op = ISTORE \/ op = LOG \/
    op = ASSERT \/ op = ASSERT_UNREACHABLE \/ op = INVOKE
Proof
  Cases >> EVAL_TAC
QED

val effect_free_opcode_tac =
  fs[step_inst_base_def] >>
  FIRST [
    drule exec_pure1_state_equiv >> simp[],
    drule exec_pure2_state_equiv >> simp[],
    drule exec_pure3_state_equiv >> simp[],
    drule exec_read0_state_equiv >> simp[],
    drule exec_read1_state_equiv >> simp[],
    gvs[AllCaseEqs()] >>
    TRY (irule state_equiv_refl) >>
    TRY (irule state_equiv_subset >> qexists_tac `{out}` >>
         simp[update_var_state_equiv, SUBSET_DEF])
  ];

Triviality step_inst_base_effect_free_state_equiv_local:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_effect_free_op_def]
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
QED

val mem_write_opcode_tac =
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  fs[exec_write2_def] >>
  gvs[AllCaseEqs()] >>
  fs[mstore_def, mstore8_def, mcopy_def, write_memory_with_expansion_def,
     lookup_var_def, update_var_def, contract_storage_def,
     write_effects_def, is_alloca_op_def];

Triviality step_inst_base_mem_write_preserves_all:
  !inst s s'. step_inst_base inst s = OK s' /\
    is_mem_write_op inst.inst_opcode ==>
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
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_mem_write_op_def]
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
QED

Triviality step_inst_base_mem_write_preserves_static_fields:
  !inst s s'. step_inst_base inst s = OK s' /\
    is_mem_write_op inst.inst_opcode ==>
    s'.vs_transient = s.vs_transient /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_accounts = s.vs_accounts /\
    contract_storage s' = contract_storage s
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_mem_write_op_def]
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
QED

(* Single mega-lemma: all fields preserved by step_inst_base for
   non-terminators. One 94-opcode case split instead of 11 separate ones.
   Also includes non-output variable preservation and conditional
   write-effects preservation (for fields not in write_effects). *)
Theorem step_inst_base_preserves_all[local]:
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
  rpt gen_tac >> strip_tac >>
  drule nonterminator_opcode_class >> strip_tac
  >- (drule_all step_inst_base_effect_free_state_equiv_local >>
      strip_tac >> drule state_equiv_step_base_concl >> simp[])
  >- (drule_all step_inst_base_mem_write_preserves_all >> simp[])
  >- (Cases_on `inst.inst_opcode` >>
      gvs[is_alloca_op_def] >>
      gvs[step_inst_base_def] >>
      step_base_field_finish_tac)
  >- (Cases_on `inst.inst_opcode` >>
      gvs[is_ext_call_op_def] >>
      gvs[step_inst_base_def] >>
      step_base_field_finish_tac)
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- gvs[step_inst_base_def]
QED

(* Generic lift: from step_inst_base mega-lemma to step_inst for any field *)
fun step_inst_lift_from_all_tac field_fn =
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  (gvs[bind_outputs_def, merge_callee_state_def] >>
   qspecl_then [field_fn] mp_tac foldl_update_var_preserves >>
   simp[update_var_def]) >>
  imp_res_tac step_inst_base_preserves_all >> gvs[is_terminator_def];

(* ===================================================================== *)
(* ===== Section 6: Write-Effects Soundness ============================ *)
(* ===================================================================== *)

(* Write-effects soundness: step_inst only modifies state fields
   listed in write_effects. 2 of 7 proved (immutables, returndata).
   Remaining 5 require EVM-level guarantees about what `run` preserves
   in static mode (STATICCALL) or CREATE/CREATE2 paths. *)

(* ===================================================================== *)
(* ===== EVM Static-Mode Invariant (upstream dependency) =============== *)
(* ===================================================================== *)

(* ---- STATICCALL Helper ----
   STATICCALL goes through exec_ext_call with value=0w, is_static=T.
   transfer_value with 0 is identity, run_static_preserves gives
   final_state.rollback = initial rollback, ctxt.logs = [].
   So accounts/transient/logs are all preserved. *)
Theorem exec_ext_call_static_preserves[local]:
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

(* ---- step_inst_base preservation for static fields ----
   Per-field lemmas for storage/transient/log/accounts.
   Same tactic pattern as step_inst_base_preserves_memory.
   STATICCALL is the only non-excluded opcode that touches these
   fields — handled by exec_ext_call_static_preserves. *)

Triviality step_inst_base_staticcall_preserves_static_fields:
  !inst s s'. step_inst_base inst s = OK s' /\
    inst.inst_opcode = STATICCALL ==>
    contract_storage s' = contract_storage s /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_accounts = s.vs_accounts
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  gvs[AllCaseEqs()] >>
  drule exec_ext_call_static_preserves >>
  simp[contract_storage_def]
QED

val state_equiv_static_field_tac =
  drule_all step_inst_base_effect_free_state_equiv_local >>
  simp[state_equiv_def, execution_equiv_def, contract_storage_def];

val step_base_mem_write_field_tac =
  TRY (Cases_on `inst.inst_opcode` >>
       gvs[is_mem_write_op_def, write_effects_def] >>
       NO_TAC) >>
  drule_all step_inst_base_mem_write_preserves_static_fields >> simp[];

val step_base_create_field_tac =
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  fs[exec_create_def, extract_venom_result_def,
     update_var_def, write_memory_with_expansion_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  gvs[update_var_def, write_memory_with_expansion_def];

val step_base_ext_call_field_tac =
  Cases_on `inst.inst_opcode` >>
  gvs[is_ext_call_op_def, write_effects_def, all_effects_def, empty_effects_def] >>
  FIRST [
    drule_all step_inst_base_staticcall_preserves_static_fields >> simp[],
    step_base_create_field_tac
  ];

val step_base_oneoff_field_tac =
  gvs[write_effects_def, all_effects_def, empty_effects_def] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  gvs[AllCaseEqs()] >>
  fs[exec_write2_def, update_var_def, sstore_def, tstore_def,
     write_memory_with_expansion_def, contract_storage_def,
     eval_operands_def] >>
  gvs[AllCaseEqs()];

val step_base_static_field_tac =
  rpt gen_tac >> strip_tac >>
  drule nonterminator_opcode_class >> strip_tac
  >- state_equiv_static_field_tac
  >- step_base_mem_write_field_tac
  >- step_base_ext_call_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac;

Theorem step_inst_base_preserves_storage[local]:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    contract_storage s' = contract_storage s
Proof
  rpt gen_tac >> strip_tac >>
  drule nonterminator_opcode_class >> strip_tac
  >- state_equiv_static_field_tac
  >- step_base_mem_write_field_tac
  >- step_base_ext_call_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
QED

Theorem step_inst_base_preserves_transient[local]:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
    s'.vs_transient = s.vs_transient
Proof
  rpt gen_tac >> strip_tac >>
  drule nonterminator_opcode_class >> strip_tac
  >- state_equiv_static_field_tac
  >- step_base_mem_write_field_tac
  >- step_base_ext_call_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
QED

Theorem step_inst_base_preserves_log[local]:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    Eff_LOG NOTIN write_effects inst.inst_opcode ==>
    s'.vs_logs = s.vs_logs
Proof
  rpt gen_tac >> strip_tac >>
  drule nonterminator_opcode_class >> strip_tac
  >- state_equiv_static_field_tac
  >- step_base_mem_write_field_tac
  >- step_base_ext_call_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
QED

Theorem step_inst_base_preserves_accounts[local]:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    s'.vs_accounts = s.vs_accounts
Proof
  rpt gen_tac >> strip_tac >>
  drule nonterminator_opcode_class >> strip_tac
  >- state_equiv_static_field_tac
  >- step_base_mem_write_field_tac
  >- step_base_ext_call_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
QED

Theorem step_inst_base_preserves_memory[local]:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
    s'.vs_memory = s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  drule nonterminator_opcode_class >> strip_tac
  >- state_equiv_static_field_tac
  >- step_base_mem_write_field_tac
  >- step_base_ext_call_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
  >- step_base_oneoff_field_tac
QED

(* ---- Write-Effects Soundness ----
   INVOKE is vacuously excluded (write_effects INVOKE = all_effects).
   Non-INVOKE reduces to step_inst_base via step_inst_non_invoke. *)

val write_effects_invoke_tac =
  gvs[write_effects_def, all_effects_def, empty_effects_def];

Theorem write_effects_sound_storage:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    contract_storage s' = contract_storage s
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_storage
QED

Theorem write_effects_sound_transient:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
    s'.vs_transient = s.vs_transient
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_transient
QED

Theorem write_effects_sound_memory:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
    s'.vs_memory = s.vs_memory
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_memory >> gvs[is_terminator_def]
QED

Theorem write_effects_sound_immutables:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_IMMUTABLES NOTIN write_effects inst.inst_opcode ==>
    s'.vs_immutables = s.vs_immutables
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_all >> gvs[is_terminator_def]
QED

Theorem write_effects_sound_returndata:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_RETURNDATA NOTIN write_effects inst.inst_opcode ==>
    s'.vs_returndata = s.vs_returndata
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_all >> gvs[is_terminator_def]
QED

Theorem write_effects_sound_log:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_LOG NOTIN write_effects inst.inst_opcode ==>
    s'.vs_logs = s.vs_logs
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_log
QED

Theorem write_effects_sound_accounts:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    s'.vs_accounts = s.vs_accounts
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_accounts
QED

(* ===================================================================== *)
(* ===== Section 7: Context Field Preservation ========================= *)
(* ===================================================================== *)

(* Exported step_inst versions — derived from mega-lemma *)
Theorem step_preserves_call_ctx:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_call_ctx = s.vs_call_ctx
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_call_ctx`
QED

Theorem step_preserves_tx_ctx:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_tx_ctx = s.vs_tx_ctx
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_tx_ctx`
QED

Theorem step_preserves_block_ctx:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_block_ctx = s.vs_block_ctx
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_block_ctx`
QED

Theorem step_preserves_code:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_code = s.vs_code
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_code`
QED

Theorem step_preserves_data_section:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_data_section = s.vs_data_section
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_data_section`
QED

Theorem step_preserves_labels:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_labels = s.vs_labels
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_labels`
QED

Theorem step_preserves_params:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_params = s.vs_params
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_params`
QED

Theorem step_preserves_prev_hashes:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_prev_hashes = s.vs_prev_hashes
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_prev_hashes`
QED

Theorem step_preserves_halted:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_halted = s.vs_halted
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_halted`
QED

Theorem step_preserves_current_bb[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_current_bb = s.vs_current_bb
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_current_bb`
QED

Theorem step_preserves_prev_bb[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_prev_bb = s.vs_prev_bb
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_prev_bb`
QED

Theorem step_preserves_control_flow:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  metis_tac[step_preserves_current_bb, step_inst_preserves_inst_idx,
            step_preserves_prev_bb]
QED

(* ===================================================================== *)
(* ===== Section 5b: Write-Opcode Class Preservation =================== *)
(* ===================================================================== *)

Theorem is_mem_write_not_terminator[local]:
  !op. is_mem_write_op op ==> ~is_terminator op
Proof
  Cases >> EVAL_TAC
QED

Theorem is_alloca_not_terminator[local]:
  !op. is_alloca_op op ==> ~is_terminator op
Proof
  Cases >> EVAL_TAC
QED

Theorem is_ext_call_not_terminator[local]:
  !op. is_ext_call_op op ==> ~is_terminator op
Proof
  Cases >> EVAL_TAC
QED

(* Full tactic for opcode-class theorems: prove all conjuncts at once
   via full case split. Avoids issues with Once/subgoal ordering. *)
val step_class_write_tac =
  rw[Once step_inst_def, step_inst_base_def] >>
  gvs[AllCaseEqs(), is_mem_write_op_def, is_alloca_op_def,
      is_ext_call_op_def, is_terminator_def] >>
  write_finish_tac;

val ext_call_opcode_tac =
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  step_base_field_finish_tac;

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
    s'.vs_labels = s.vs_labels /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_mem_write_op_def, Once step_inst_def]
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
QED

Theorem step_alloca_preserves:
  !fuel ctx inst s s'.
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
    s'.vs_labels = s.vs_labels /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def, Once step_inst_def] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  step_base_field_finish_tac
QED

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
    s'.vs_labels = s.vs_labels /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_ext_call_op_def, Once step_inst_def]
  >- ext_call_opcode_tac
  >- ext_call_opcode_tac
  >- ext_call_opcode_tac
  >- ext_call_opcode_tac
  >- ext_call_opcode_tac
QED

(* ===================================================================== *)
(* ===== Section 4: Non-Output Variable Preservation =================== *)
(* ===================================================================== *)

(* Helper: FOLDL of update_var preserves lookup_var for non-output vars *)
Theorem foldl_update_var_lookup[local]:
  !kvs s v. ~MEM v (MAP FST kvs) ==>
    lookup_var v (FOLDL (\s' (k,w). update_var k w s') s kvs) = lookup_var v s
Proof
  Induct >> simp[pairTheory.FORALL_PROD] >>
  rw[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem step_preserves_non_output_vars:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    !v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  (* INVOKE case *)
  (gvs[bind_outputs_def, merge_callee_state_def] >>
   `~MEM v (MAP FST (ZIP (inst.inst_outputs, vals)))` by
     simp[listTheory.MAP_ZIP] >>
   drule foldl_update_var_lookup >> simp[lookup_var_def]) >>
  (* Non-INVOKE: use mega-lemma *)
  metis_tac[step_inst_base_preserves_all, is_terminator_def]
QED

Theorem step_write2_preserves_all_vars:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    (inst.inst_opcode = MSTORE \/ inst.inst_opcode = MSTORE8 \/
     inst.inst_opcode = SSTORE \/ inst.inst_opcode = TSTORE) ==>
    !v. lookup_var v s' = lookup_var v s
Proof
  rpt strip_tac >> gvs[] >>
  imp_res_tac step_mstore_preserves >> gvs[] >>
  imp_res_tac step_mstore8_preserves >> gvs[] >>
  imp_res_tac step_sstore_preserves >> gvs[] >>
  imp_res_tac step_tstore_preserves >> gvs[]
QED

(* ===================================================================== *)
(* ===== Section 3b: step_effect_free_state_equiv ====================== *)
(* ===================================================================== *)

(* step_inst_base level: effect-free opcodes produce state_equiv *)
Theorem step_inst_base_effect_free_state_equiv:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rpt strip_tac >>
  drule_all step_inst_base_effect_free_state_equiv_local >> simp[]
QED

Theorem step_effect_free_state_equiv:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by (CCONTR_TAC >> gvs[is_effect_free_op_def]) >>
  `step_inst_base inst s = OK s'` by metis_tac[step_inst_non_invoke] >>
  metis_tac[step_inst_base_effect_free_state_equiv]
QED

(* ===================================================================== *)
(* ===== Section 8: Derived Equivalences =============================== *)
(* ===================================================================== *)

Theorem step_effect_free_execution_equiv:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    execution_equiv (set inst.inst_outputs) s s'
Proof
  rpt strip_tac >>
  imp_res_tac step_effect_free_state_equiv >>
  gvs[state_equiv_def]
QED

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
  rpt strip_tac >>
  `state_equiv (set inst1.inst_outputs) s s1`
    by metis_tac[step_effect_free_state_equiv] >>
  `state_equiv (set inst2.inst_outputs) s s2`
    by metis_tac[step_effect_free_state_equiv] >>
  gvs[state_equiv_def, execution_equiv_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `MEM v (inst1.inst_outputs)` >> gvs[] >>
  metis_tac[]
QED
