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
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_fmp = s.vs_fmp /\
    s'.vs_call_entry_fmp = s.vs_call_entry_fmp /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    s'.vs_return_pc_token = s.vs_return_pc_token
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

(* Index the exported equations once; rewrite only the known opcode branch. *)
val step_inst_base_opcode_rewrites = let
  fun key th = let
    val (_, body) = strip_forall (concl th)
    val (guard, _) = dest_imp body
  in rhs guard end
in map (fn th => (key th, th))
  (CONJUNCTS venomExecSemanticsTheory.step_inst_base_opcode_eqs) end;

fun rewrite_step_inst_base_opcode eq = let
  val (_, rewrite) = valOf (List.find
    (fn (key, _) => aconv key (rhs (concl eq)))
    step_inst_base_opcode_rewrites)
in PURE_ONCE_REWRITE_TAC [MATCH_MP rewrite eq] end;

val step_inst_base_opcode_tac =
  qpat_assum `inst.inst_opcode = _` rewrite_step_inst_base_opcode;

(* NOP is identity: produces OK with unchanged state *)
val reduce_to_base_tac =
  rw[Once step_inst_def] >> step_inst_base_opcode_tac >> simp[];

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
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum `step_inst_base` mp_tac >>
  step_inst_base_opcode_tac >> strip_tac >> gvs[AllCaseEqs()]
QED

Theorem step_assert_unreachable_identity:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode = ASSERT_UNREACHABLE ==>
    s' = s
Proof
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum `step_inst_base` mp_tac >>
  step_inst_base_opcode_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

(* ===================================================================== *)
(* ===== Section 5: Write-Opcode Field Preservation ==================== *)
(* ===================================================================== *)

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
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum`step_inst_base`mp_tac >>
  step_inst_base_opcode_tac >>
  strip_tac >> gvs[exec_write2_def,AllCaseEqs()] >>
  simp[mstore_def, lookup_var_def]
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
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum`step_inst_base`mp_tac >>
  step_inst_base_opcode_tac >>
  strip_tac >> gvs[exec_write2_def,AllCaseEqs()] >>
  simp[mstore8_def, lookup_var_def]
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
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum`step_inst_base`mp_tac >>
  step_inst_base_opcode_tac >>
  strip_tac >> gvs[exec_write2_def,AllCaseEqs()] >>
  simp[sstore_def, lookup_var_def]
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
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum`step_inst_base`mp_tac >>
  step_inst_base_opcode_tac >>
  strip_tac >> gvs[exec_write2_def,AllCaseEqs()] >>
  simp[tstore_def, lookup_var_def]
QED

Theorem step_istore_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = ISTORE ==>
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
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum`step_inst_base`mp_tac >>
  step_inst_base_opcode_tac >>
  strip_tac >> gvs[exec_write2_def,AllCaseEqs()] >>
  simp[istore_def, mstore_def, lookup_var_def]
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
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum`step_inst_base`mp_tac >>
  step_inst_base_opcode_tac >>
  strip_tac >> gvs[exec_write2_def,AllCaseEqs()] >>
  simp[lookup_var_def]
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
     istore_def, write_memory_with_expansion_def, mcopy_def,
     revert_state_def, eval_operands_def,
     lookup_var_def, FLOOKUP_UPDATE];

val step_base_field_tac =
  rw[step_inst_base_def] >> step_base_field_finish_tac;

val step_base_field_opcode_tac =
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  step_inst_base_opcode_tac >> strip_tac >> step_base_field_finish_tac;

Triviality nonterminator_opcode_class:
  !op. ~is_terminator op ==>
    is_effect_free_op op \/
    is_mem_write_op op \/
    is_alloca_op op \/
    is_ext_call_op op \/
    op = SSTORE \/ op = TSTORE \/ op = ISTORE \/ op = LOG \/
    op = SETFMP \/ op = DALLOCA \/
    op = ASSERT \/ op = ASSERT_UNREACHABLE \/ op = INVOKE
Proof
  Cases >> EVAL_TAC
QED

val effect_free_opcode_tac =
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  step_inst_base_opcode_tac >> strip_tac >>
  FIRST [
    drule exec_pure1_state_equiv >> simp[],
    drule exec_pure2_state_equiv >> simp[],
    drule exec_pure3_state_equiv >> simp[],
    drule exec_read0_state_equiv >> simp[],
    drule exec_read1_state_equiv >> simp[],
    gvs[AllCaseEqs()] >>
    TRY (rename1 `state_equiv {ptr_out; next_out} _ _` >>
         simp[state_equiv_def, execution_equiv_def, update_var_def,
              lookup_var_def, FLOOKUP_UPDATE]) >>
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
  (* 1--10 *)
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
  (* 11--20 *)
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
  (* 21--30 *)
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
  (* 31--40 *)
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
  (* 41--50 *)
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
  (* 51--60 *)
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
  (* 61--66 *)
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
QED

Theorem pack_dret_dynamic_preserves_non_memory:
  !pairs cursor s ptrs final_cursor s'.
    pack_dret_dynamic cursor pairs s = (ptrs,final_cursor,s') ==>
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
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_vars = s.vs_vars /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_call_entry_fmp = s.vs_call_entry_fmp /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    s'.vs_return_pc_token = s.vs_return_pc_token
Proof
  Induct >- simp[pack_dret_dynamic_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[Once pack_dret_dynamic_def] >>
  pairarg_tac >> gvs[] >>
  first_x_assum drule >>
  simp[mcopy_def, write_memory_with_expansion_def] >>
  rpt strip_tac >> gvs[]
QED

val mem_write_opcode_tac =
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  step_inst_base_opcode_tac >>
  strip_tac >>
  fs[exec_write2_def] >>
  gvs[AllCaseEqs()] >>
  fs[mstore_def, mstore8_def, mcopy_def, write_memory_with_expansion_def,
     lookup_var_def, update_var_def, contract_storage_def,
     write_effects_def, is_alloca_op_def] >>
  TRY (pairarg_tac >> gvs[] >>
       drule pack_dret_dynamic_preserves_non_memory >> simp[]);

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
     s'.vs_returndata = s.vs_returndata) /\
    s'.vs_fmp = s.vs_fmp /\
    s'.vs_call_entry_fmp = s.vs_call_entry_fmp /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    s'.vs_return_pc_token = s.vs_return_pc_token
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
  >- mem_write_opcode_tac
QED

(* Reject non-call opcodes without traversing the large frame conclusion. *)
val ext_call_opcode_filter_tac = let
  val ss = bool_ss ++ rewrites [is_ext_call_op_def]
in
  qpat_x_assum `is_ext_call_op _`
    (CHECK_ASSUME_TAC o SIMP_RULE ss [])
end;

(* Only classification, opcode equality and finite effect-set computation. *)
val ext_call_frame_simp_tac = let
  val ss = bool_ss ++ simpLib.type_ssfrag ``:opcode`` ++
    simpLib.type_ssfrag ``:effect`` ++ rewrites
      [is_alloca_op_def, write_effects_def, all_effects_def,
       IN_DIFF, IN_INSERT, NOT_IN_EMPTY]
in simp_tac ss [] end;

(* Project only the residual call frame before inspecting result cases.
   Computed accounts, memory, return data and EVM results remain opaque. *)
val ext_call_frame = ``\t:venom_state.
  t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_code = s.vs_code /\
  t.vs_data_section = s.vs_data_section /\
  t.vs_labels = s.vs_labels /\
  t.vs_params = s.vs_params /\
  t.vs_prev_hashes = s.vs_prev_hashes /\
  t.vs_halted = s.vs_halted /\
  t.vs_current_bb = s.vs_current_bb /\
  t.vs_prev_bb = s.vs_prev_bb /\
  (!v. ~MEM v inst.inst_outputs ==> lookup_var v t = lookup_var v s) /\
  t.vs_immutables = s.vs_immutables /\
  t.vs_fmp = s.vs_fmp /\
  t.vs_call_entry_fmp = s.vs_call_entry_fmp /\
  t.vs_initial_fmp = s.vs_initial_fmp /\
  t.vs_return_pc_token = s.vs_return_pc_token``;

val ext_call_frame_result = BETA_RULE (prove (
  ``!r s'. r = OK s' ==>
    ((case r of OK t => ^ext_call_frame t | _ => T) ==>
     ^ext_call_frame s')``,
  rpt strip_tac >> gvs[]));

val ext_call_frame_projection_rewrites = let
  val defs = [exec_ext_call_def, venomCallOracleDefsTheory.consume_call_outcome_eq,
    venomCallOracleDefsTheory.consume_create_outcome_eq,
    exec_delegatecall_def, exec_create_def, extract_venom_result_def,
    step_inst_base_def]
  fun case_type tm = let val (_, arg, _) = TypeBase.dest_case tm
                     in type_of arg end
  val shapes = mk_set (List.concat (map
    (map case_type o find_terms TypeBase.is_case o concl) defs))
  val tests = map (rhs o concl o
    (DEPTH_CONV BETA_CONV THENC REWRITE_CONV
      [lookup_var_def, update_var_def, venom_state_accfupds,
       combinTheory.K_THM, FLOOKUP_UPDATE]))
    [``\r:exec_result. case r of OK t => ^ext_call_frame t | _ => T``,
     ``\r:(bytes32 # venom_state) option.
       case r of NONE => T | SOME p => ^ext_call_frame (SND p)``,
     ``\r:(bytes32 # venom_state) option.
       case r of NONE => T | SOME p =>
         ^ext_call_frame (update_var out (FST p) (SND p))``,
     ``\r:(bytes32 # venom_state) option.
       case r of NONE => T | SOME p =>
         case inst.inst_outputs of
           [out] => ^ext_call_frame (update_var out (FST p) (SND p))
         | _ => T``]
  fun project test ty = BETA_RULE (ISPEC test (TypeBase.case_rand_of ty))
  fun constant ty = Prim_rec.prove_case_const_thm
    {case_def = TypeBase.case_def_of ty,
     nchotomy = TypeBase.nchotomy_of ty}
in List.concat (map (fn test => map (project test) shapes @
     [BETA_RULE (PART_MATCH (rator o lhs) COND_RAND test)]) tests) @
   map constant shapes end;

val ext_call_frame_projection_ss = pure_ss ++ boolSimps.BOOL_ss ++ rewrites
  ([listTheory.list_case_def, pairTheory.pair_CASE_def,
    optionTheory.option_case_def, pairTheory.ELIM_UNCURRY,
    pairTheory.FST, pairTheory.SND, LET_THM, listTheory.MEM,
    TypeBase.one_one_of ``:exec_result``,
    TypeBase.distinct_of ``:exec_result``,
    TypeBase.case_def_of ``:exec_result``,
    venom_state_accfupds, combinTheory.K_THM,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE] @
   ext_call_frame_projection_rewrites);

fun ext_call_frame_cases_tac ss =
  asm_simp_tac ss [] >>
  REPEAT (BasicProvers.PURE_TOP_CASE_TAC >> asm_simp_tac ss []) >>
  rpt strip_tac >> asm_simp_tac bool_ss [boolTheory.EQ_SYM_EQ];

(* Cache the helper boundary once, not once per operand envelope. *)
val ext_call_frame_helper_rewrites = let
  val ss = ext_call_frame_projection_ss ++ rewrites
    [exec_ext_call_def, venomCallOracleDefsTheory.consume_call_outcome_eq,
    venomCallOracleDefsTheory.consume_create_outcome_eq,
     exec_delegatecall_def, exec_create_def, extract_venom_result_def]
  val tests =
    [``case exec_ext_call inst s gas addr value ao az ro rz static of
         OK t => ^ext_call_frame t | _ => T``,
     ``case exec_delegatecall inst s gas addr ao az ro rz of
         OK t => ^ext_call_frame t | _ => T``,
     ``case exec_create inst s value off sz salt of
         OK t => ^ext_call_frame t | _ => T``]
in map (fn tm => REWRITE_RULE [lookup_var_def]
  (BETA_RULE (prove (tm, ext_call_frame_cases_tac ss)))) tests end;

val ext_call_frame_body_tac = let
  val ss = ext_call_frame_projection_ss ++ rewrites ext_call_frame_helper_rewrites
in
  strip_tac >>
  qpat_x_assum `_ = OK _`
    (fn eq => MATCH_MP_TAC (MATCH_MP ext_call_frame_result eq)) >>
  ext_call_frame_cases_tac ss
end;

(* Single mega-lemma: all fields preserved by step_inst_base for
   non-terminators. One 94-opcode case split instead of 11 separate ones.
   Also includes non-output variable preservation and conditional
   write-effects preservation (for fields not in write_effects). *)
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
     s'.vs_returndata = s.vs_returndata) /\
    (inst.inst_opcode <> SETFMP /\ inst.inst_opcode <> DALLOCA /\
     ~is_alloca_op inst.inst_opcode ==> s'.vs_fmp = s.vs_fmp) /\
    s'.vs_call_entry_fmp = s.vs_call_entry_fmp /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    s'.vs_return_pc_token = s.vs_return_pc_token
Proof
  rpt gen_tac >> strip_tac >>
  drule nonterminator_opcode_class >> strip_tac
  >- (drule_all step_inst_base_effect_free_state_equiv_local >>
      strip_tac >> drule state_equiv_step_base_concl >> simp[])
  >- (drule_all step_inst_base_mem_write_preserves_all >> simp[])
  >- (Cases_on `inst.inst_opcode` >>
      gvs[is_alloca_op_def] >>
      step_base_field_opcode_tac)
  >- suspend"g1"
  >- step_base_field_opcode_tac
  >- step_base_field_opcode_tac
  >- step_base_field_opcode_tac
  >- step_base_field_opcode_tac
  >- step_base_field_opcode_tac
  >- step_base_field_opcode_tac
  >- step_base_field_opcode_tac
  >- step_base_field_opcode_tac
  >- step_base_field_opcode_tac
QED

Resume step_inst_base_preserves_all[g1]:
      Cases_on `inst.inst_opcode` >>
      ext_call_opcode_filter_tac >>
      ext_call_frame_simp_tac >>
      qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
      step_inst_base_opcode_tac >>
      ext_call_frame_body_tac
QED

Finalise step_inst_base_preserves_all

Theorem step_inst_base_preserves_fmp_ordinary:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> SETFMP /\
    inst.inst_opcode <> DALLOCA ==>
    s'.vs_fmp = s.vs_fmp
Proof
  rpt strip_tac >>
  drule step_inst_base_preserves_all >> simp[]
QED

(* Generic lift: from step_inst_base mega-lemma to step_inst for any field *)
fun step_inst_lift_from_all_tac field_fn =
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  (gvs[bind_outputs_def, adopt_return_fmp_def, merge_callee_state_def] >>
   qspecl_then [field_fn] mp_tac foldl_update_var_preserves >>
   simp[update_var_def]) >>
  imp_res_tac step_inst_base_preserves_all >> gvs[is_terminator_def];
