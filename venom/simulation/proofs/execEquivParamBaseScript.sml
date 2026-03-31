(*
 * Parameterized Execution Equivalence — Base Helpers
 *
 * Core valid_state_rel lemmas and exec_*-level helpers.
 * Used by execEquivParamHelpers (step_inst-level proofs).
 *)

Theory execEquivParamBase
Ancestors
  execEquivParamDefs passSimulationDefs stateEquivProps execEquivProps
  stateEquiv venomInst venomExecSemantics venomState
Libs
  finite_mapTheory listTheory rich_listTheory

open execEquivParamLib

(* ==========================================================================
   Core helpers extracted from valid_state_rel
   ========================================================================== *)

Theorem vsr_eval_operand:
  !R_ok R_term op s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    (!x. op = Var x ==> lookup_var x s1 = lookup_var x s2) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  rw[valid_state_rel_def] >> metis_tac[]
QED

Theorem vsr_eval_operands:
  !R_ok R_term ops s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    (!x. MEM (Var x) ops ==> lookup_var x s1 = lookup_var x s2) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct_on `ops` >> rw[eval_operands_def] >>
  `eval_operand h s1 = eval_operand h s2` by (
    irule vsr_eval_operand >> metis_tac[]) >>
  simp[] >>
  `eval_operands ops s1 = eval_operands ops s2` by (
    first_x_assum (qspecl_then [`R_ok`, `R_term`, `s1`, `s2`] mp_tac) >>
    simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem vsr_R_ok_fields:
  !R_ok R_term s1 s2. valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_params = s2.vs_params /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas
Proof
  rw[valid_state_rel_def]
QED

Theorem vsr_R_term_fields:
  !R_ok R_term s1 s2. valid_state_rel R_ok R_term /\ R_term s1 s2 ==>
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_params = s2.vs_params /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas
Proof
  rw[valid_state_rel_def]
QED

Theorem vsr_R_ok_R_term:
  !R_ok R_term s1 s2. valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_term s1 s2
Proof
  rw[valid_state_rel_def]
QED

Theorem vsr_update_var_R_ok:
  !R_ok R_term x v s1 s2. valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (update_var x v s1) (update_var x v s2)
Proof
  rw[valid_state_rel_def]
QED

Theorem vsr_update_var_R_term:
  !R_ok R_term x v s1 s2. valid_state_rel R_ok R_term /\ R_term s1 s2 ==>
    R_term (update_var x v s1) (update_var x v s2)
Proof
  rw[valid_state_rel_def]
QED

Theorem vsr_R_ok_refl:
  !R_ok R_term s. valid_state_rel R_ok R_term ==> R_ok s s
Proof
  rw[valid_state_rel_def]
QED

Theorem vsr_R_term_refl:
  !R_ok R_term s. valid_state_rel R_ok R_term ==> R_term s s
Proof
  rw[valid_state_rel_def]
QED

(* ==========================================================================
   Field-update helpers
   ========================================================================== *)

Theorem vsr_halted_R_ok:
  !R_ok R_term b s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (s1 with vs_halted := b) (s2 with vs_halted := b)
Proof
  vsr_field_update_proof ()
QED

Theorem vsr_halted_R_term:
  !R_ok R_term b s1 s2.
    valid_state_rel R_ok R_term /\ R_term s1 s2 ==>
    R_term (s1 with vs_halted := b) (s2 with vs_halted := b)
Proof
  vsr_field_update_R_term_proof ()
QED

Theorem vsr_memory_R_ok:
  !R_ok R_term m s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (s1 with vs_memory := m) (s2 with vs_memory := m)
Proof
  vsr_field_update_proof ()
QED

Theorem vsr_returndata_R_ok:
  !R_ok R_term rd s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (s1 with vs_returndata := rd) (s2 with vs_returndata := rd)
Proof
  vsr_field_update_proof ()
QED

Theorem vsr_returndata_R_term:
  !R_ok R_term rd s1 s2.
    valid_state_rel R_ok R_term /\ R_term s1 s2 ==>
    R_term (s1 with vs_returndata := rd) (s2 with vs_returndata := rd)
Proof
  vsr_field_update_R_term_proof ()
QED

Theorem vsr_transient_R_ok:
  !R_ok R_term t s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (s1 with vs_transient := t) (s2 with vs_transient := t)
Proof
  vsr_field_update_proof ()
QED

Theorem vsr_logs_R_ok:
  !R_ok R_term l s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (s1 with vs_logs := l) (s2 with vs_logs := l)
Proof
  vsr_field_update_proof ()
QED

Theorem vsr_accounts_R_ok:
  !R_ok R_term a s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (s1 with vs_accounts := a) (s2 with vs_accounts := a)
Proof
  vsr_field_update_proof ()
QED

Theorem vsr_immutables_R_ok:
  !R_ok R_term im s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (s1 with vs_immutables := im) (s2 with vs_immutables := im)
Proof
  vsr_field_update_proof ()
QED

Theorem vsr_allocas_R_ok:
  !R_ok R_term al s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (s1 with vs_allocas := al) (s2 with vs_allocas := al)
Proof
  vsr_field_update_proof ()
QED

Theorem vsr_inst_idx_R_ok:
  !R_ok R_term n s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (s1 with vs_inst_idx := n) (s2 with vs_inst_idx := n)
Proof
  vsr_field_update_proof ()
QED

Theorem vsr_inst_idx_R_term:
  !R_ok R_term n s1 s2.
    valid_state_rel R_ok R_term /\ R_term s1 s2 ==>
    R_term (s1 with vs_inst_idx := n) (s2 with vs_inst_idx := n)
Proof
  vsr_field_update_R_term_proof ()
QED

(* ==========================================================================
   Composite state update helpers
   ========================================================================== *)

Theorem vsr_terminal_R_term:
  !R_ok R_term s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_term (halt_state s1) (halt_state s2) /\
    R_term (revert_state s1) (revert_state s2)
Proof
  rw[halt_state_def, revert_state_def] >>
  imp_res_tac vsr_R_ok_R_term >>
  metis_tac[vsr_halted_R_term]
QED

Theorem vsr_set_returndata_R_term:
  !R_ok R_term v s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_term (set_returndata v s1) (set_returndata v s2)
Proof
  rw[set_returndata_def] >>
  imp_res_tac vsr_R_ok_R_term >>
  metis_tac[vsr_returndata_R_term]
QED

Theorem vsr_jump_to:
  !R_ok R_term lbl s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (jump_to lbl s1) (jump_to lbl s2)
Proof
  rpt strip_tac >> simp[jump_to_def] >>
  vsr_reconstruct_R_ok_tac `s1` `s2`
QED

Theorem vsr_write_memory:
  !R_ok R_term off bytes s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (write_memory_with_expansion off bytes s1)
         (write_memory_with_expansion off bytes s2)
Proof
  rw[write_memory_with_expansion_def, LET_THM] >>
  imp_res_tac vsr_R_ok_fields >> gvs[] >>
  vsr_reconstruct_R_ok_tac `s1` `s2`
QED

Theorem vsr_mstore:
  !R_ok R_term off v s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (mstore off v s1) (mstore off v s2)
Proof
  rw[mstore_def, LET_THM] >>
  imp_res_tac vsr_R_ok_fields >> gvs[] >>
  vsr_reconstruct_R_ok_tac `s1` `s2`
QED

Theorem vsr_mstore8:
  !R_ok R_term off v s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (mstore8 off v s1) (mstore8 off v s2)
Proof
  rw[mstore8_def, LET_THM] >>
  imp_res_tac vsr_R_ok_fields >> gvs[] >>
  vsr_reconstruct_R_ok_tac `s1` `s2`
QED

Theorem vsr_sstore:
  !R_ok R_term k v s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (sstore k v s1) (sstore k v s2)
Proof
  rw[sstore_def] >> imp_res_tac vsr_R_ok_fields >> gvs[] >>
  vsr_reconstruct_R_ok_tac `s1` `s2`
QED

Theorem vsr_tstore:
  !R_ok R_term k v s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (tstore k v s1) (tstore k v s2)
Proof
  rw[tstore_def] >> imp_res_tac vsr_R_ok_fields >> gvs[] >>
  vsr_reconstruct_R_ok_tac `s1` `s2`
QED

Theorem vsr_mcopy:
  !R_ok R_term dst src sz s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (mcopy dst src sz s1) (mcopy dst src sz s2)
Proof
  rw[mcopy_def] >> imp_res_tac vsr_R_ok_fields >> gvs[] >>
  vsr_irule vsr_write_memory >> simp[]
QED

Theorem resolve_phi_MEM:
  !prev_bb ops op. resolve_phi prev_bb ops = SOME op ==> MEM op ops
Proof
  ho_match_mp_tac resolve_phi_ind >> rw[resolve_phi_def] >> rw[] >> metis_tac[]
QED

(* ==========================================================================
   Category helpers: exec_* preserves lift_result R_ok R_term
   ========================================================================== *)

fun vsr_eval_ops_tac () =
  `!op. MEM op inst.inst_operands ==>
     eval_operand op s1 = eval_operand op s2` by (
    rw[] >> vsr_irule vsr_eval_operand >> simp[] >> metis_tac[])

Theorem vsr_exec_pure1:
  !R_ok R_term f inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (exec_pure1 f inst s1) (exec_pure1 f inst s2)
Proof
  rw[exec_pure1_def] >> vsr_eval_ops_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_update_var_R_ok >> simp[]
QED

Theorem vsr_exec_pure2:
  !R_ok R_term f inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (exec_pure2 f inst s1) (exec_pure2 f inst s2)
Proof
  rw[exec_pure2_def] >> vsr_eval_ops_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_update_var_R_ok >> simp[]
QED

Theorem vsr_exec_pure3:
  !R_ok R_term f inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (exec_pure3 f inst s1) (exec_pure3 f inst s2)
Proof
  rw[exec_pure3_def] >> vsr_eval_ops_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_update_var_R_ok >> simp[]
QED

Theorem vsr_exec_read0:
  !R_ok R_term f inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    f s1 = f s2 ==>
    lift_result R_ok R_term (exec_read0 f inst s1) (exec_read0 f inst s2)
Proof
  rw[exec_read0_def] >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_update_var_R_ok >> simp[]
QED

Theorem vsr_exec_read1:
  !R_ok R_term f inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    (!v. f v s1 = f v s2) /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (exec_read1 f inst s1) (exec_read1 f inst s2)
Proof
  rw[exec_read1_def] >> vsr_eval_ops_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_update_var_R_ok >> simp[]
QED

Theorem vsr_exec_write2:
  !R_ok R_term f inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    (!v1 v2. R_ok (f v1 v2 s1) (f v1 v2 s2)) /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (exec_write2 f inst s1) (exec_write2 f inst s2)
Proof
  rw[exec_write2_def] >> vsr_eval_ops_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def])
QED

(* ==========================================================================
   External call helpers
   ========================================================================== *)

fun ext_call_result_tac () =
  vsr_irule vsr_update_var_R_ok >> simp[] >>
  vsr_reconstruct_R_ok_tac `s1` `s2`

fun ext_call_proof_tac def_thms =
  rw(LET_THM :: def_thms) >>
  imp_res_tac vsr_R_ok_fields >> gvs[] >>
  simp[read_memory_def, make_venom_call_state_def,
       make_venom_delegatecall_state_def, make_venom_create_state_def,
       make_sub_tx_def, make_rollback_def, venom_to_tx_params_def,
       LET_THM] >>
  simp[extract_venom_result_def] >>
  rpt CASE_TAC >> gvs[lift_result_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  ext_call_result_tac ()

Theorem vsr_exec_ext_call:
  !R_ok R_term inst s1 s2 gas addr value ao as_ ro rs is_static.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    lift_result R_ok R_term
      (exec_ext_call inst s1 gas addr value ao as_ ro rs is_static)
      (exec_ext_call inst s2 gas addr value ao as_ ro rs is_static)
Proof
  ext_call_proof_tac [exec_ext_call_def]
QED

Theorem vsr_exec_delegatecall:
  !R_ok R_term inst s1 s2 gas addr ao as_ ro rs.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    lift_result R_ok R_term
      (exec_delegatecall inst s1 gas addr ao as_ ro rs)
      (exec_delegatecall inst s2 gas addr ao as_ ro rs)
Proof
  ext_call_proof_tac [exec_delegatecall_def]
QED

Theorem vsr_exec_create:
  !R_ok R_term inst s1 s2 value offset sz salt_opt.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    lift_result R_ok R_term
      (exec_create inst s1 value offset sz salt_opt)
      (exec_create inst s2 value offset sz salt_opt)
Proof
  Cases_on `salt_opt` >>
  ext_call_proof_tac [exec_create_def]
QED

Theorem vsr_exec_alloca:
  !R_ok R_term inst s1 s2 alloc_size.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    lift_result R_ok R_term
      (exec_alloca inst s1 alloc_size)
      (exec_alloca inst s2 alloc_size)
Proof
  rw[exec_alloca_def, next_alloca_offset_def, LET_THM] >>
  imp_res_tac vsr_R_ok_fields >> gvs[] >>
  rpt CASE_TAC >> gvs[lift_result_def] >>
  ext_call_result_tac ()
QED

(* ==========================================================================
   Helpers for run_block_preserves_R
   ========================================================================== *)

Theorem FIND_MEM:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l` >> rw[FIND_thm] >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem vsr_setup_callee_eq:
  !R_ok R_term fn args s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    setup_callee fn args s1 = setup_callee fn args s2
Proof
  rw[setup_callee_def] >> imp_res_tac vsr_R_ok_fields >>
  gvs[venom_state_component_equality]
QED

Theorem vsr_merge_callee_R_ok:
  !R_ok R_term s1 s2 c.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (merge_callee_state s1 c) (merge_callee_state s2 c)
Proof
  rw[merge_callee_state_def] >> vsr_reconstruct_R_ok_tac `s1` `s2`
QED

Theorem vsr_foldl_update_var_R_ok:
  !R_ok R_term kvs s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (FOLDL (\s' (k,v). update_var k v s') s1 kvs)
         (FOLDL (\s' (k,v). update_var k v s') s2 kvs)
Proof
  gen_tac >> gen_tac >> Induct >> rw[] >> pairarg_tac >> gvs[] >>
  first_x_assum irule >> simp[] >>
  irule vsr_update_var_R_ok >> metis_tac[]
QED

Theorem vsr_bind_outputs_R_ok:
  !R_ok R_term outs vals s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    OPTREL R_ok (bind_outputs outs vals s1) (bind_outputs outs vals s2)
Proof
  rw[bind_outputs_def] >>
  irule vsr_foldl_update_var_R_ok >> metis_tac[]
QED

Theorem vsr_next_inst_R_ok:
  !R_ok R_term s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (next_inst s1) (next_inst s2)
Proof
  rw[next_inst_def] >> imp_res_tac vsr_R_ok_fields >> gvs[] >>
  vsr_irule vsr_inst_idx_R_ok >> simp[]
QED

val _ = export_theory()
